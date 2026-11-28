//! Diagnostics: who writes one word of title memory. `VICTORY_WATCH=<expr>`
//! (an expression of `VICTORY_PEEK`'s syntax, whose byte count, 1, 2, 4 or
//! 8, is the watched width; the address must be aligned to it) puts a
//! hardware write breakpoint (debug register 0) on that address on every
//! thread. Each write is counted. The first `VICTORY_WATCH_MAX` (10) are
//! logged with the thread, the 24 bytes there after it and the stack; the
//! last 48 are kept, and printed once no write has come for 3 s (the last
//! writes before a hang: who took a lock that is never let go). A count is
//! logged every 5 s. Off unless set.
//!
//! Title objects are made at run time, so the address is often unknown at
//! the start. If the expression reads a pointer, the image slot it reads
//! first is watched from the start (debug register 1): when the title
//! writes it, the address is worked out there and then, the writing thread
//! watches it at once and the others within a few milliseconds. Threads
//! made later are added every 250 ms. At the start a thread of ours writes
//! a word of its own under debug register 2, to show that writes trap.

use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use windows_sys::Win32::Foundation::{CloseHandle, EXCEPTION_SINGLE_STEP};
use windows_sys::Win32::System::Diagnostics::Debug::{
    AddVectoredExceptionHandler, CONTEXT, CONTEXT_DEBUG_REGISTERS_AMD64, EXCEPTION_POINTERS,
    GetThreadContext, SetThreadContext,
};
use windows_sys::Win32::System::Threading::{
    GetCurrentThreadId, GetCurrentThreadStackLimits, OpenThread, ResumeThread, SuspendThread,
    THREAD_GET_CONTEXT, THREAD_SET_CONTEXT, THREAD_SUSPEND_RESUME,
};

use crate::crash::{MAX_FRAMES, locate, unwind_into};
use crate::peek::Watched;

const CONTINUE_EXECUTION: i32 = -1;
const CONTINUE_SEARCH: i32 = 0;
/// DR6: a single step (the other bits: debug register n matched).
const BS: u64 = 1 << 14;
const KEPT: usize = 48;
const FRAMES: usize = 14;
/// Debug registers: the watched word, the pointer slot, the self-test.
const WORD: usize = 0;
const SLOT: usize = 1;
const TEST: usize = 2;

static ADDRESS: AtomicUsize = AtomicUsize::new(0);
static SLOT_AT: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(8);
static BASE: AtomicUsize = AtomicUsize::new(0);
static WRITES: AtomicU64 = AtomicU64::new(0);
static SLOT_WRITES: AtomicU64 = AtomicU64::new(0);
static TEST_WRITES: AtomicU64 = AtomicU64::new(0);
static LOGGED_MOST: AtomicU64 = AtomicU64::new(10);
static TEST_WORD: AtomicU64 = AtomicU64::new(0);

static WATCHED: OnceLock<Watched> = OnceLock::new();
static ARMER: OnceLock<std::thread::Thread> = OnceLock::new();

struct Write {
    n: u64,
    thread: u32,
    ms: u128,
    after: [u64; 3],
    frames: Vec<u64>,
}

static LAST: Mutex<VecDeque<Write>> = Mutex::new(VecDeque::new());
static START: OnceLock<Instant> = OnceLock::new();

#[repr(C, align(16))]
struct Aligned(CONTEXT);

fn len_bits(bytes: usize) -> u64 {
    match bytes {
        1 => 0b00,
        2 => 0b01,
        8 => 0b10,
        _ => 0b11,
    }
}

/// DR7 with debug register `n` set to break on writes of `bytes` there.
fn dr7(old: u64, n: usize, bytes: usize) -> u64 {
    let (enable, field) = (1u64 << (2 * n), 16 + 4 * n);
    (old & !(0b1111 << field)) | enable | (0b01 << field) | (len_bits(bytes) << (field + 2))
}

/// Puts `(register, address, bytes)` into `context`'s debug registers.
fn set(context: &mut CONTEXT, regs: &[(usize, usize, usize)]) {
    for &(n, at, bytes) in regs {
        let at = at as u64;
        match n {
            0 => context.Dr0 = at,
            1 => context.Dr1 = at,
            2 => context.Dr2 = at,
            _ => context.Dr3 = at,
        }
        context.Dr7 = dr7(context.Dr7, n, bytes);
    }
}

/// Sets debug registers on `id` (not this thread). Whether it took.
fn arm(id: u32, regs: &[(usize, usize, usize)]) -> bool {
    // SAFETY: a thread of our own process, suspended while its debug
    // registers are read and written, then resumed.
    unsafe {
        let thread = OpenThread(
            THREAD_SUSPEND_RESUME | THREAD_GET_CONTEXT | THREAD_SET_CONTEXT,
            0,
            id,
        );
        if thread.is_null() {
            return false;
        }
        let mut ok = false;
        if SuspendThread(thread) != u32::MAX {
            let mut context = Aligned(std::mem::zeroed());
            context.0.ContextFlags = CONTEXT_DEBUG_REGISTERS_AMD64;
            if GetThreadContext(thread, &mut context.0) != 0 {
                set(&mut context.0, regs);
                ok = SetThreadContext(thread, &context.0) != 0;
            }
            ResumeThread(thread);
        }
        CloseHandle(thread);
        ok
    }
}

/// The registers every thread should have now.
fn wanted() -> Vec<(usize, usize, usize)> {
    let mut regs = Vec::new();
    let slot = SLOT_AT.load(Ordering::Acquire);
    if slot != 0 {
        regs.push((SLOT, slot, 8));
    }
    let at = ADDRESS.load(Ordering::Acquire);
    if at != 0 {
        regs.push((WORD, at, BYTES.load(Ordering::Relaxed)));
    }
    regs
}

/// Whether a write by a thread of ours under debug register 2 traps.
fn self_test() -> bool {
    let (go, wait) = std::sync::mpsc::channel::<()>();
    let (id_tx, id_rx) = std::sync::mpsc::channel();
    let Ok(writer) = std::thread::Builder::new()
        .name("victory-watch-test".into())
        .spawn(move || {
            // SAFETY: a plain query.
            let _ = id_tx.send(unsafe { GetCurrentThreadId() });
            let _ = wait.recv();
            TEST_WORD.store(1, Ordering::SeqCst);
        })
    else {
        return false;
    };
    let Ok(id) = id_rx.recv() else { return false };
    let armed = arm(id, &[(TEST, TEST_WORD.as_ptr() as usize, 8)]);
    let _ = go.send(());
    let _ = writer.join();
    armed && TEST_WRITES.load(Ordering::Relaxed) == 1
}

fn show(w: &Write) -> String {
    let stack: Vec<String> = w.frames.iter().map(|&f| locate(f as usize)).collect();
    format!(
        "write {} at {} ms, thread {}, then {:#018x} {:#018x} {:#018x}: {}",
        w.n,
        w.ms,
        w.thread,
        w.after[0],
        w.after[1],
        w.after[2],
        stack.join(" < ")
    )
}

/// Takes the address from the expression if it reads now and is aligned.
fn try_resolve() -> Option<usize> {
    let watched = WATCHED.get()?;
    let found = (watched.resolve)(BASE.load(Ordering::Relaxed) as u64)?;
    (found % watched.bytes.max(1) as u64 == 0).then_some(found as usize)
}

/// Starts watching for the title's image at `base`, if asked.
pub(crate) fn start(base: usize) {
    let Ok(value) = std::env::var("VICTORY_WATCH") else {
        return;
    };
    let Some(watched) = crate::peek::parse_one(&value) else {
        tracing::warn!(value, "VICTORY_WATCH: no expression parsed");
        return;
    };
    if let Some(n) = std::env::var("VICTORY_WATCH_MAX")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
    {
        LOGGED_MOST.store(n, Ordering::Relaxed);
    }
    START.get_or_init(Instant::now);
    BASE.store(base, Ordering::Relaxed);
    BYTES.store(watched.bytes, Ordering::Relaxed);
    if let Some(rva) = watched.first_pointer {
        SLOT_AT.store(base + rva as usize, Ordering::Release);
    }
    let text = watched.text.clone();
    let _ = WATCHED.set(watched);
    // SAFETY: a handler that lives as long as the process; first in line.
    unsafe { AddVectoredExceptionHandler(1, Some(handler)) };
    let tested = self_test();
    tracing::info!(
        expr = %text,
        traps = tested,
        "VICTORY_WATCH: self-test (a write of ours under a debug register {})",
        if tested { "trapped" } else { "did NOT trap: the watch cannot work here" }
    );
    if let Some(at) = try_resolve() {
        ADDRESS.store(at, Ordering::Release);
    }
    let spawned = std::thread::Builder::new()
        .name("victory-watch".into())
        .spawn(move || {
            let mut armed: HashMap<u32, Vec<(usize, usize, usize)>> = HashMap::new();
            let mut told = 0usize;
            let (mut seen, mut changed, mut shown, mut counted) =
                (0u64, Instant::now(), 0u64, Instant::now());
            let mut first = true;
            loop {
                if !first {
                    std::thread::park_timeout(Duration::from_millis(250));
                }
                first = false;
                if ADDRESS.load(Ordering::Acquire) == 0
                    && let Some(at) = try_resolve()
                {
                    ADDRESS.store(at, Ordering::Release);
                }
                let at = ADDRESS.load(Ordering::Acquire);
                if at != told {
                    told = at;
                    tracing::info!(
                        expr = %text,
                        address = format_args!("{at:#x}"),
                        ms = START.get().map_or(0, |s| s.elapsed().as_millis()),
                        "VICTORY_WATCH: watching"
                    );
                }
                let regs = wanted();
                for id in crate::stacks::other_threads() {
                    if armed.get(&id) != Some(&regs) && arm(id, &regs) {
                        armed.insert(id, regs.clone());
                    }
                }
                let n = WRITES.load(Ordering::Relaxed);
                if n != seen {
                    (seen, changed) = (n, Instant::now());
                } else if n != shown && changed.elapsed() >= Duration::from_secs(3) {
                    shown = n;
                    let last = LAST.lock().unwrap_or_else(|e| e.into_inner());
                    tracing::info!(
                        writes = n,
                        "VICTORY_WATCH: no write for 3 s; the last {}:",
                        last.len()
                    );
                    for w in last.iter() {
                        tracing::info!("VICTORY_WATCH {}", show(w));
                    }
                }
                if counted.elapsed() >= Duration::from_secs(5) {
                    counted = Instant::now();
                    tracing::info!(
                        writes = n,
                        pointer_writes = SLOT_WRITES.load(Ordering::Relaxed),
                        threads = armed.len(),
                        "VICTORY_WATCH writes so far"
                    );
                }
            }
        });
    match spawned {
        Ok(handle) => {
            let _ = ARMER.set(handle.thread().clone());
        }
        Err(e) => tracing::warn!(error = %e, "VICTORY_WATCH: no thread"),
    }
}

/// Records a write of the watched word by this thread.
fn record(context: &CONTEXT, at: usize) {
    let n = WRITES.fetch_add(1, Ordering::Relaxed) + 1;
    let (mut low, mut high) = (0, 0);
    // SAFETY: writes this thread's stack bounds.
    unsafe { GetCurrentThreadStackLimits(&mut low, &mut high) };
    let mut frames = Vec::with_capacity(MAX_FRAMES);
    unwind_into(*context, low, high, &mut frames, true);
    frames.truncate(FRAMES);
    // SAFETY: the watched address was readable when it was chosen and the
    // write that trapped has just gone to it.
    let after = unsafe { std::array::from_fn(|i| ((at as *const u64).add(i)).read_volatile()) };
    let write = Write {
        n,
        // SAFETY: a plain query.
        thread: unsafe { GetCurrentThreadId() },
        ms: START.get().map_or(0, |s| s.elapsed().as_millis()),
        after,
        frames,
    };
    if n <= LOGGED_MOST.load(Ordering::Relaxed) {
        tracing::info!("VICTORY_WATCH {}", show(&write));
    }
    let mut last = LAST.lock().unwrap_or_else(|e| e.into_inner());
    if last.len() == KEPT {
        last.pop_front();
    }
    last.push_back(write);
}

unsafe extern "system" fn handler(info: *mut EXCEPTION_POINTERS) -> i32 {
    // SAFETY: the system passes a live record and context.
    let (record_, context) = unsafe { (&*(*info).ExceptionRecord, &mut *(*info).ContextRecord) };
    let matched = context.Dr6 & 0b111;
    if record_.ExceptionCode != EXCEPTION_SINGLE_STEP || matched == 0 {
        return CONTINUE_SEARCH;
    }
    let stepping = context.Dr6 & BS != 0;
    context.Dr6 &= !0b111;
    if matched & (1 << TEST) != 0 {
        TEST_WRITES.fetch_add(1, Ordering::Relaxed);
    }
    if matched & (1 << SLOT) != 0 {
        let n = SLOT_WRITES.fetch_add(1, Ordering::Relaxed) + 1;
        let now = try_resolve();
        if n <= 4 {
            tracing::info!(
                write = n,
                // SAFETY: a plain query.
                thread = unsafe { GetCurrentThreadId() },
                ms = START.get().map_or(0, |s| s.elapsed().as_millis()),
                address = format_args!("{:#x}", now.unwrap_or(0)),
                "VICTORY_WATCH: the pointer slot was written"
            );
        }
        if let Some(at) = now
            && ADDRESS.swap(at, Ordering::AcqRel) != at
        {
            // This thread at once; the others as soon as the armer runs.
            context.ContextFlags |= CONTEXT_DEBUG_REGISTERS_AMD64;
            set(context, &[(WORD, at, BYTES.load(Ordering::Relaxed))]);
            if let Some(armer) = ARMER.get() {
                armer.unpark();
            }
        }
    }
    if matched & (1 << WORD) != 0 {
        let at = ADDRESS.load(Ordering::Acquire);
        if at != 0 {
            record(context, at);
        }
    }
    // A single step of `VICTORY_BREAK`'s on the same instruction is its own.
    if stepping {
        CONTINUE_SEARCH
    } else {
        CONTINUE_EXECUTION
    }
}

#[cfg(test)]
mod tests {
    use super::dr7;

    #[test]
    fn dr7_sets_a_register_for_writes_of_the_width() {
        assert_eq!(dr7(0, 0, 8), 1 | 0b01 << 16 | 0b10 << 18);
        assert_eq!(dr7(0xF_0003, 0, 4), 3 | 0b01 << 16 | 0b11 << 18);
        assert_eq!(dr7(1, 1, 8), 1 | 1 << 2 | 0b01 << 20 | 0b10 << 22);
        assert_eq!(dr7(0, 2, 1), 1 << 4 | 0b01 << 24);
    }
}
