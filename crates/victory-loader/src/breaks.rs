//! Diagnostics: who runs a piece of title code, and how often.
//! `VICTORY_BREAK=<rva>[,<rva>...]` (hex, with or without `0x`) puts a
//! breakpoint on each instruction at the image base plus `rva`; each hit is
//! counted, the first `VICTORY_BREAK_MAX` (20) of each are logged with the
//! thread and its stack, and every 5 s a line gives the counts so far (so
//! the log shows when a function stops being run). The original byte is put
//! back for one instruction (single step) and the breakpoint set again.
//! An `rva` must be the start of an instruction. A hit on another thread
//! while one is stepping over the breakpoint is missed: counts are at least
//! what they say. Off unless set.

use std::cell::Cell;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use windows_sys::Win32::Foundation::{EXCEPTION_BREAKPOINT, EXCEPTION_SINGLE_STEP};
use windows_sys::Win32::System::Diagnostics::Debug::{
    AddVectoredExceptionHandler, EXCEPTION_POINTERS, FlushInstructionCache,
};
use windows_sys::Win32::System::Memory::{PAGE_EXECUTE_READWRITE, VirtualProtect};
use windows_sys::Win32::System::Threading::{GetCurrentProcess, GetCurrentThreadId, GetCurrentThreadStackLimits};

use crate::crash::{MAX_FRAMES, locate, unwind_into};

const MOST: usize = 16;
const CONTINUE_EXECUTION: i32 = -1;
const CONTINUE_SEARCH: i32 = 0;
const TRAP_FLAG: u32 = 0x100;

/// Each breakpoint: its address (0: unused), the byte it covers, its hits.
static AT: [AtomicUsize; MOST] = [const { AtomicUsize::new(0) }; MOST];
static ORIGINAL: [AtomicUsize; MOST] = [const { AtomicUsize::new(0) }; MOST];
static HITS: [AtomicU64; MOST] = [const { AtomicU64::new(0) }; MOST];
static BASE: AtomicUsize = AtomicUsize::new(0);
static LOGGED_MOST: AtomicU64 = AtomicU64::new(20);

thread_local! {
    /// The breakpoint this thread is stepping over (its slot plus one).
    static STEPPING: Cell<usize> = const { Cell::new(0) };
}

fn parse(value: &str) -> Vec<usize> {
    value
        .split(',')
        .filter_map(|s| {
            let s = s.trim();
            usize::from_str_radix(s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s), 16).ok()
        })
        .take(MOST)
        .collect()
}

/// Writes `byte` at `at` (code: made writable first) and flushes it.
///
/// # Safety
/// `at` is a byte of the title's mapped code.
unsafe fn poke(at: usize, byte: u8) {
    // SAFETY: as the caller says; the page stays executable.
    unsafe {
        (at as *mut u8).write_volatile(byte);
        FlushInstructionCache(GetCurrentProcess(), at as *const _, 1);
    }
}

/// Sets the breakpoints for the title's image at `base`, if asked.
pub(crate) fn start(base: usize) {
    let Ok(value) = std::env::var("VICTORY_BREAK") else {
        return;
    };
    let rvas = parse(&value);
    if rvas.is_empty() {
        tracing::warn!(value, "VICTORY_BREAK: no address parsed");
        return;
    }
    if let Some(n) = std::env::var("VICTORY_BREAK_MAX").ok().and_then(|v| v.trim().parse::<u64>().ok()) {
        LOGGED_MOST.store(n, Ordering::Relaxed);
    }
    BASE.store(base, Ordering::Relaxed);
    // SAFETY: a handler that lives as long as the process; first in line.
    unsafe { AddVectoredExceptionHandler(1, Some(handler)) };
    for (slot, rva) in rvas.into_iter().enumerate() {
        let at = base + rva;
        let mut old = 0;
        // SAFETY: a page of the title's mapped image, made writable for the
        // breakpoint and left executable.
        let writable = unsafe { VirtualProtect(at as *const _, 1, PAGE_EXECUTE_READWRITE, &mut old) } != 0;
        if !writable {
            tracing::warn!(rva = format_args!("{rva:#x}"), "VICTORY_BREAK: the code could not be made writable");
            continue;
        }
        // SAFETY: as above; the original byte is kept to put back.
        let byte = unsafe { (at as *const u8).read_volatile() };
        ORIGINAL[slot].store(usize::from(byte), Ordering::Relaxed);
        AT[slot].store(at, Ordering::Release);
        // SAFETY: as above.
        unsafe { poke(at, 0xCC) };
        tracing::info!(rva = format_args!("{rva:#x}"), original = format_args!("{byte:#04x}"), "VICTORY_BREAK: set");
    }
    let spawned = std::thread::Builder::new().name("victory-breaks".into()).spawn(|| {
        loop {
            std::thread::sleep(std::time::Duration::from_secs(5));
            let counts: Vec<String> = (0..MOST)
                .filter_map(|i| {
                    let at = AT[i].load(Ordering::Relaxed);
                    (at != 0).then(|| format!("{:#x}: {}", at - BASE.load(Ordering::Relaxed), HITS[i].load(Ordering::Relaxed)))
                })
                .collect();
            tracing::info!("VICTORY_BREAK hits so far: {}", counts.join(", "));
        }
    });
    if let Err(e) = spawned {
        tracing::warn!(error = %e, "VICTORY_BREAK: no thread for the counts");
    }
}

unsafe extern "system" fn handler(info: *mut EXCEPTION_POINTERS) -> i32 {
    // SAFETY: the system passes a live record and context.
    let (record, context) = unsafe { (&*(*info).ExceptionRecord, &mut *(*info).ContextRecord) };
    if record.ExceptionCode == EXCEPTION_SINGLE_STEP {
        let slot = STEPPING.with(|s| s.replace(0));
        if slot == 0 {
            return CONTINUE_SEARCH;
        }
        // SAFETY: the breakpoint's own address, in the title's code.
        unsafe { poke(AT[slot - 1].load(Ordering::Relaxed), 0xCC) };
        return CONTINUE_EXECUTION;
    }
    if record.ExceptionCode != EXCEPTION_BREAKPOINT {
        return CONTINUE_SEARCH;
    }
    let pc = record.ExceptionAddress as usize;
    let Some(slot) = (0..MOST).find(|&i| AT[i].load(Ordering::Acquire) == pc) else {
        return CONTINUE_SEARCH;
    };
    let n = HITS[slot].fetch_add(1, Ordering::Relaxed) + 1;
    if n <= LOGGED_MOST.load(Ordering::Relaxed) {
        let (mut low, mut high) = (0, 0);
        // SAFETY: writes this thread's stack bounds.
        unsafe { GetCurrentThreadStackLimits(&mut low, &mut high) };
        let mut frames = Vec::with_capacity(MAX_FRAMES);
        unwind_into(*context, low, high, &mut frames, true);
        let stack: Vec<String> = frames.iter().take(16).map(|&f| locate(f as usize)).collect();
        // SAFETY: a plain query.
        let thread = unsafe { GetCurrentThreadId() };
        tracing::info!(
            rva = format_args!("{:#x}", pc - BASE.load(Ordering::Relaxed)),
            hit = n,
            thread,
            "VICTORY_BREAK hit: {}",
            stack.join(" < ")
        );
    }
    // Step over the original instruction, then set the breakpoint again.
    // SAFETY: the breakpoint's own address and the byte it covered.
    unsafe { poke(pc, ORIGINAL[slot].load(Ordering::Relaxed) as u8) };
    STEPPING.with(|s| s.set(slot + 1));
    context.EFlags |= TRAP_FLAG;
    CONTINUE_EXECUTION
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn addresses_parse_in_hex() {
        assert_eq!(parse("0x43AE230, 6d8da0 ,zz"), vec![0x43AE230, 0x6D8DA0]);
    }
}
