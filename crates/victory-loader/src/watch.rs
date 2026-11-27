//! Diagnostics: who writes one word of title memory. `VICTORY_WATCH=<expr>`
//! (an expression of `VICTORY_PEEK`'s syntax, whose byte count, 1, 2, 4 or
//! 8, is the watched width; the address must be aligned to it) puts a
//! hardware write breakpoint (debug register 0) on that address on every
//! thread, once the address can be read; threads made later are added
//! every 250 ms. Each write is counted. The first `VICTORY_WATCH_MAX` (10)
//! are logged with the thread, the 24 bytes there after it and the stack;
//! the last 48 are kept, and printed once no write has come for 3 s (the
//! last writes before a hang: who took a lock that is never let go).
//! A count is logged every 5 s. Off unless set.

use std::collections::{HashSet, VecDeque};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
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

const CONTINUE_EXECUTION: i32 = -1;
const CONTINUE_SEARCH: i32 = 0;
/// DR6: debug register 0 matched; a single step.
const B0: u64 = 1;
const BS: u64 = 1 << 14;
const KEPT: usize = 48;
const FRAMES: usize = 14;

static ADDRESS: AtomicUsize = AtomicUsize::new(0);
static WRITES: AtomicU64 = AtomicU64::new(0);
static LOGGED_MOST: AtomicU64 = AtomicU64::new(10);

struct Write {
    n: u64,
    thread: u32,
    ms: u128,
    after: [u64; 3],
    frames: Vec<u64>,
}

static LAST: Mutex<VecDeque<Write>> = Mutex::new(VecDeque::new());
static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();

#[repr(C, align(16))]
struct Aligned(CONTEXT);

/// DR7 with debug register 0 set to break on writes of `bytes` there.
fn dr7(old: u64, bytes: usize) -> u64 {
    let len = match bytes {
        1 => 0b00,
        2 => 0b01,
        8 => 0b10,
        _ => 0b11,
    };
    (old & !(0b1111 << 16 | 0b11)) | 1 | (0b01 << 16) | (len << 18)
}

/// Sets debug register 0 on `id` (not this thread). Whether it took.
fn arm(id: u32, at: usize, bytes: usize) -> bool {
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
                context.0.Dr0 = at as u64;
                context.0.Dr7 = dr7(context.0.Dr7, bytes);
                ok = SetThreadContext(thread, &context.0) != 0;
            }
            ResumeThread(thread);
        }
        CloseHandle(thread);
        ok
    }
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

/// Starts watching for the title's image at `base`, if asked.
pub(crate) fn start(base: usize) {
    let Ok(value) = std::env::var("VICTORY_WATCH") else {
        return;
    };
    let Some((resolve, bytes, text)) = crate::peek::parse_one(&value) else {
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
    // SAFETY: a handler that lives as long as the process; first in line.
    unsafe { AddVectoredExceptionHandler(1, Some(handler)) };
    let spawned = std::thread::Builder::new().name("victory-watch".into()).spawn(move || {
        let mut armed = HashSet::new();
        let mut at = 0usize;
        let (mut seen, mut changed, mut shown, mut counted) = (0u64, Instant::now(), 0u64, Instant::now());
        loop {
            std::thread::sleep(Duration::from_millis(250));
            if at == 0 {
                let Some(found) = resolve(base as u64) else { continue };
                if found % bytes.max(1) as u64 != 0 {
                    tracing::warn!(address = format_args!("{found:#x}"), bytes, "VICTORY_WATCH: address not aligned to its width; not watched");
                    return;
                }
                at = found as usize;
                ADDRESS.store(at, Ordering::Release);
                tracing::info!(expr = %text, address = format_args!("{at:#x}"), bytes, "VICTORY_WATCH: watching");
            }
            for id in crate::stacks::other_threads() {
                if !armed.contains(&id) && arm(id, at, bytes) {
                    armed.insert(id);
                }
            }
            let n = WRITES.load(Ordering::Relaxed);
            if n != seen {
                (seen, changed) = (n, Instant::now());
            } else if n != shown && changed.elapsed() >= Duration::from_secs(3) {
                shown = n;
                let last = LAST.lock().unwrap_or_else(|e| e.into_inner());
                tracing::info!(writes = n, "VICTORY_WATCH: no write for 3 s; the last {}:", last.len());
                for w in last.iter() {
                    tracing::info!("VICTORY_WATCH {}", show(w));
                }
            }
            if counted.elapsed() >= Duration::from_secs(5) {
                counted = Instant::now();
                tracing::info!(writes = n, threads = armed.len(), "VICTORY_WATCH writes so far");
            }
        }
    });
    if let Err(e) = spawned {
        tracing::warn!(error = %e, "VICTORY_WATCH: no thread");
    }
}

unsafe extern "system" fn handler(info: *mut EXCEPTION_POINTERS) -> i32 {
    // SAFETY: the system passes a live record and context.
    let (record, context) = unsafe { (&*(*info).ExceptionRecord, &mut *(*info).ContextRecord) };
    if record.ExceptionCode != EXCEPTION_SINGLE_STEP || context.Dr6 & B0 == 0 {
        return CONTINUE_SEARCH;
    }
    let at = ADDRESS.load(Ordering::Acquire);
    let stepping = context.Dr6 & BS != 0;
    context.Dr6 &= !B0;
    if at == 0 {
        return if stepping {
            CONTINUE_SEARCH
        } else {
            CONTINUE_EXECUTION
        };
    }
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
    {
        let mut last = LAST.lock().unwrap_or_else(|e| e.into_inner());
        if last.len() == KEPT {
            last.pop_front();
        }
        last.push_back(write);
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
    fn dr7_sets_register_0_for_writes_of_the_width() {
        assert_eq!(dr7(0, 8), 1 | 0b01 << 16 | 0b10 << 18);
        assert_eq!(dr7(0xF_0003, 4), 1 | 0b01 << 16 | 0b11 << 18);
        assert_eq!(dr7(1 << 2, 1), 1 << 2 | 1 | 0b01 << 16);
    }
}
