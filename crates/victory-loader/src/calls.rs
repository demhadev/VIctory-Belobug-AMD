//! Diagnostics: who takes and lets go of one title lock.
//! `VICTORY_LOCK_CALLS=<rva>><offset>@<sign><site>:<len>[,<sign><site>:<len>...]`
//! (hex): the lock is the pointer at the image base plus `rva`, plus
//! `offset`, read afresh on every call, so a lock made at any time is
//! caught from its first use. Each site is the entry of a function taking
//! the lock in `rcx`; `+` marks a take, `-` a release; `len` is how many
//! bytes of whole instructions at its entry are moved to a trampoline (at
//! least 5, none of them relative to `rip`, `rax` and the flags free there).
//! A call with that lock traps; others pass through at the cost of a
//! compare. Each trap is counted and kept (the last 48, with the thread,
//! the lock's first 24 bytes before the call and the caller's stack); per
//! thread, takes less releases and the stack of its last take are kept.
//! Once no call has come for 3 s, all of it is printed: a thread left
//! holding the lock shows where it took it. Off unless set.

use std::collections::{HashMap, VecDeque};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use windows_sys::Win32::Foundation::EXCEPTION_BREAKPOINT;
use windows_sys::Win32::System::Diagnostics::Debug::{
    AddVectoredExceptionHandler, CONTEXT, EXCEPTION_POINTERS, FlushInstructionCache,
};
use windows_sys::Win32::System::Memory::{
    MEM_COMMIT, MEM_RESERVE, PAGE_EXECUTE_READWRITE, VirtualAlloc, VirtualProtect,
};
use windows_sys::Win32::System::Threading::{
    GetCurrentProcess, GetCurrentThreadId, GetCurrentThreadStackLimits,
};

use crate::crash::{MAX_FRAMES, locate, unwind_into};

const CONTINUE_EXECUTION: i32 = -1;
const CONTINUE_SEARCH: i32 = 0;
const MOST: usize = 8;
const KEPT: usize = 48;
const FRAMES: usize = 14;
const STUB: usize = 64;

/// Each site: the trampoline's int3 (0: unused), whether it takes, its count.
static TRAP: [AtomicUsize; MOST] = [const { AtomicUsize::new(0) }; MOST];
static TAKES: [AtomicUsize; MOST] = [const { AtomicUsize::new(0) }; MOST];
static RVA: [AtomicUsize; MOST] = [const { AtomicUsize::new(0) }; MOST];
static COUNT: [AtomicU64; MOST] = [const { AtomicU64::new(0) }; MOST];
static ALL: AtomicU64 = AtomicU64::new(0);
static LOGGED_MOST: AtomicU64 = AtomicU64::new(10);
static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();

#[derive(Clone)]
struct Call {
    n: u64,
    rva: usize,
    take: bool,
    thread: u32,
    ms: u128,
    before: [u64; 3],
    frames: Vec<u64>,
}

#[derive(Default)]
struct State {
    last: VecDeque<Call>,
    /// Per thread: takes less releases, and its last take.
    held: HashMap<u32, (i64, Option<Call>)>,
}

static STATE: Mutex<Option<State>> = Mutex::new(None);

#[derive(Debug, PartialEq, Eq)]
struct Spec {
    slot: usize,
    offset: u32,
    sites: Vec<(bool, usize, usize)>,
}

fn hex(s: &str) -> Option<usize> {
    let s = s.trim();
    usize::from_str_radix(
        s.strip_prefix("0x")
            .or_else(|| s.strip_prefix("0X"))
            .unwrap_or(s),
        16,
    )
    .ok()
}

fn parse(value: &str) -> Option<Spec> {
    let (lock, sites) = value.split_once('@')?;
    let (slot, offset) = lock.split_once('>')?;
    let sites = sites
        .split(',')
        .map(|s| {
            let s = s.trim();
            let (take, rest) = match s.as_bytes().first()? {
                b'+' => (true, &s[1..]),
                b'-' => (false, &s[1..]),
                _ => return None,
            };
            let (rva, len) = rest.split_once(':')?;
            let len = hex(len)?;
            (5..=16).contains(&len).then_some((take, hex(rva)?, len))
        })
        .collect::<Option<Vec<_>>>()?;
    (!sites.is_empty() && sites.len() <= MOST).then_some(Spec {
        slot: hex(slot)?,
        offset: u32::try_from(hex(offset)?)
            .ok()
            .filter(|&o| o < 0x8000_0000)?,
        sites,
    })
}

/// The trampoline for a site at `at` whose first `len` bytes are `moved`:
/// traps if `[slot]` is not null and `[slot] + offset == rcx`, then runs
/// the moved bytes and jumps back. Returns the code and the int3's offset.
fn stub(slot: usize, offset: u32, moved: &[u8], back: usize) -> (Vec<u8>, usize) {
    let mut code = vec![0x48, 0xA1]; // mov rax, [slot]
    code.extend((slot as u64).to_le_bytes());
    code.extend([0x48, 0x85, 0xC0]); // test rax, rax
    code.extend([0x74, 0x0C]); // jz past the int3
    code.extend([0x48, 0x05]); // add rax, offset
    code.extend(offset.to_le_bytes());
    code.extend([0x48, 0x39, 0xC8]); // cmp rax, rcx
    code.extend([0x75, 0x01]); // jne past the int3
    let trap = code.len();
    code.push(0xCC);
    code.extend(moved);
    code.extend([0xFF, 0x25, 0, 0, 0, 0]); // jmp [rip]
    code.extend((back as u64).to_le_bytes());
    (code, trap)
}

/// Memory for the trampolines within a rel32 jump of the image at `base`.
fn near(base: usize, size: usize) -> Option<usize> {
    let step = 0x1_0000;
    (1..0x7000).find_map(|k| {
        let at = base.checked_sub(k * step)?;
        // SAFETY: asks for fresh memory at a free address; fails if taken.
        let got = unsafe {
            VirtualAlloc(
                at as *const _,
                size,
                MEM_RESERVE | MEM_COMMIT,
                PAGE_EXECUTE_READWRITE,
            )
        };
        (!got.is_null()).then_some(got as usize)
    })
}

/// Hooks the sites for the title's image at `base`, if asked.
pub(crate) fn start(base: usize) {
    let Ok(value) = std::env::var("VICTORY_LOCK_CALLS") else {
        return;
    };
    let Some(spec) = parse(&value) else {
        tracing::warn!(
            value,
            "VICTORY_LOCK_CALLS: not understood (rva>offset@+site:len,-site:len)"
        );
        return;
    };
    if let Some(n) = std::env::var("VICTORY_LOCK_CALLS_MAX")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
    {
        LOGGED_MOST.store(n, Ordering::Relaxed);
    }
    START.get_or_init(Instant::now);
    *STATE.lock().unwrap_or_else(|e| e.into_inner()) = Some(State::default());
    let Some(memory) = near(base, STUB * MOST) else {
        tracing::warn!("VICTORY_LOCK_CALLS: no memory near the image");
        return;
    };
    // SAFETY: a handler that lives as long as the process; first in line.
    unsafe { AddVectoredExceptionHandler(1, Some(handler)) };
    for (i, &(take, rva, len)) in spec.sites.iter().enumerate() {
        let at = base + rva;
        let here = memory + i * STUB;
        // SAFETY: `len` bytes of the title's mapped code, not yet running.
        let moved = unsafe { std::slice::from_raw_parts(at as *const u8, len) }.to_vec();
        let (code, trap) = stub(base + spec.slot, spec.offset, &moved, at + len);
        let rel = (here as i64) - (at as i64 + 5);
        let Ok(rel) = i32::try_from(rel) else {
            tracing::warn!(
                rva = format_args!("{rva:#x}"),
                "VICTORY_LOCK_CALLS: trampoline out of reach"
            );
            continue;
        };
        let mut old = 0;
        // SAFETY: our trampoline memory, and the site's bytes made writable
        // and left executable; the title does not run yet.
        unsafe {
            std::ptr::copy_nonoverlapping(code.as_ptr(), here as *mut u8, code.len());
            if VirtualProtect(at as *const _, len, PAGE_EXECUTE_READWRITE, &mut old) == 0 {
                tracing::warn!(
                    rva = format_args!("{rva:#x}"),
                    "VICTORY_LOCK_CALLS: site not writable"
                );
                continue;
            }
            TRAP[i].store(here + trap, Ordering::Relaxed);
            TAKES[i].store(usize::from(take), Ordering::Relaxed);
            RVA[i].store(rva, Ordering::Release);
            let site = at as *mut u8;
            site.write(0xE9);
            site.add(1)
                .cast::<[u8; 4]>()
                .write_unaligned(rel.to_le_bytes());
            for k in 5..len {
                site.add(k).write(0x90);
            }
            FlushInstructionCache(GetCurrentProcess(), at as *const _, len);
        }
        let bytes: Vec<String> = moved.iter().map(|b| format!("{b:02x}")).collect();
        tracing::info!(
            rva = format_args!("{rva:#x}"),
            take,
            moved = bytes.join(" "),
            "VICTORY_LOCK_CALLS: hooked"
        );
    }
    let spawned = std::thread::Builder::new()
        .name("victory-lock-calls".into())
        .spawn(|| {
            let (mut seen, mut changed, mut shown, mut counted) =
                (0u64, Instant::now(), 0u64, Instant::now());
            loop {
                std::thread::sleep(Duration::from_millis(250));
                let n = ALL.load(Ordering::Relaxed);
                if n != seen {
                    (seen, changed) = (n, Instant::now());
                } else if n != shown && changed.elapsed() >= Duration::from_secs(3) {
                    shown = n;
                    report(n);
                }
                if counted.elapsed() >= Duration::from_secs(5) {
                    counted = Instant::now();
                    let counts: Vec<String> = (0..MOST)
                        .filter(|&i| TRAP[i].load(Ordering::Relaxed) != 0)
                        .map(|i| {
                            format!(
                                "{:#x}: {}",
                                RVA[i].load(Ordering::Relaxed),
                                COUNT[i].load(Ordering::Relaxed)
                            )
                        })
                        .collect();
                    tracing::info!(
                        calls = n,
                        "VICTORY_LOCK_CALLS so far: {}",
                        counts.join(", ")
                    );
                }
            }
        });
    if let Err(e) = spawned {
        tracing::warn!(error = %e, "VICTORY_LOCK_CALLS: no thread");
    }
}

fn show(c: &Call) -> String {
    let stack: Vec<String> = c.frames.iter().map(|&f| locate(f as usize)).collect();
    format!(
        "call {} at {} ms: {} at {:#x} by thread {}, lock before {:#018x} {:#018x} {:#018x}: {}",
        c.n,
        c.ms,
        if c.take { "take" } else { "release" },
        c.rva,
        c.thread,
        c.before[0],
        c.before[1],
        c.before[2],
        stack.join(" < ")
    )
}

fn report(n: u64) {
    let state = STATE.lock().unwrap_or_else(|e| e.into_inner());
    let Some(state) = state.as_ref() else { return };
    tracing::info!(
        calls = n,
        "VICTORY_LOCK_CALLS: no call for 3 s; threads whose takes and releases differ:"
    );
    for (thread, (net, last)) in &state.held {
        if *net != 0 {
            tracing::info!(
                "VICTORY_LOCK_CALLS thread {thread}: takes less releases {net}; its last take: {}",
                last.as_ref().map_or_else(|| "none kept".to_owned(), show)
            );
        }
    }
    tracing::info!("VICTORY_LOCK_CALLS: the last {} calls:", state.last.len());
    for c in &state.last {
        tracing::info!("VICTORY_LOCK_CALLS {}", show(c));
    }
}

unsafe extern "system" fn handler(info: *mut EXCEPTION_POINTERS) -> i32 {
    // SAFETY: the system passes a live record and context.
    let (record, context) = unsafe { (&*(*info).ExceptionRecord, &mut *(*info).ContextRecord) };
    if record.ExceptionCode != EXCEPTION_BREAKPOINT {
        return CONTINUE_SEARCH;
    }
    let pc = record.ExceptionAddress as usize;
    let Some(i) = (0..MOST).find(|&i| TRAP[i].load(Ordering::Relaxed) == pc) else {
        return CONTINUE_SEARCH;
    };
    context.Rip = pc as u64 + 1;
    COUNT[i].fetch_add(1, Ordering::Relaxed);
    let n = ALL.fetch_add(1, Ordering::Relaxed) + 1;
    let take = TAKES[i].load(Ordering::Relaxed) != 0;
    // At the function's entry: the caller's frame is the return address
    // with the stack above it.
    let mut caller: CONTEXT = *context;
    // SAFETY: at a function's entry `rsp` points at the return address.
    caller.Rip = unsafe { (context.Rsp as *const u64).read() };
    caller.Rsp = context.Rsp + 8;
    let (mut low, mut high) = (0, 0);
    // SAFETY: writes this thread's stack bounds.
    unsafe { GetCurrentThreadStackLimits(&mut low, &mut high) };
    let mut frames = Vec::with_capacity(MAX_FRAMES);
    unwind_into(caller, low, high, &mut frames, true);
    frames.truncate(FRAMES);
    let lock = context.Rcx as *const u64;
    // SAFETY: the title is about to read the lock there itself.
    let before = unsafe { std::array::from_fn(|k| lock.add(k).read_volatile()) };
    let call = Call {
        n,
        rva: RVA[i].load(Ordering::Relaxed),
        take,
        // SAFETY: a plain query.
        thread: unsafe { GetCurrentThreadId() },
        ms: START.get().map_or(0, |s| s.elapsed().as_millis()),
        before,
        frames,
    };
    if n <= LOGGED_MOST.load(Ordering::Relaxed) {
        tracing::info!("VICTORY_LOCK_CALLS {}", show(&call));
    }
    let mut state = STATE.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(state) = state.as_mut() {
        let held = state.held.entry(call.thread).or_default();
        held.0 += if take { 1 } else { -1 };
        if take {
            held.1 = Some(call.clone());
        }
        push(&mut state.last, call);
    }
    CONTINUE_EXECUTION
}

fn push(last: &mut VecDeque<Call>, call: Call) {
    if last.len() == KEPT {
        last.pop_front();
    }
    last.push_back(call);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spec_parses() {
        let s = parse("9AE99B8>3CED0@+4B40:5, -0x4D9DAB0:6").unwrap();
        assert_eq!(
            s,
            Spec {
                slot: 0x9AE99B8,
                offset: 0x3CED0,
                sites: vec![(true, 0x4B40, 5), (false, 0x4D9DAB0, 6)]
            }
        );
        assert!(parse("9AE99B8>3CED0@4B40:5").is_none());
        assert!(parse("9AE99B8>3CED0@+4B40:3").is_none());
    }

    #[test]
    fn the_stub_compares_and_jumps_back() {
        let (code, trap) = stub(
            0x1122,
            0x3CED0,
            &[0x41, 0x57, 0x41, 0x56, 0x56],
            0x1_4000_4B45,
        );
        assert_eq!(code[trap], 0xCC);
        // The jz skips add (6), cmp (3), jne (2) and the int3 (1).
        assert_eq!(&code[10..15], &[0x48, 0x85, 0xC0, 0x74, 0x0C]);
        assert_eq!(trap, 15 + 11);
        assert_eq!(&code[trap + 1..trap + 6], &[0x41, 0x57, 0x41, 0x56, 0x56]);
        assert_eq!(&code[code.len() - 8..], &0x1_4000_4B45u64.to_le_bytes());
    }
}
