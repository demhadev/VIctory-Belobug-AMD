//! Diagnostics: title memory read by image offsets while the title runs.
//! `VICTORY_PEEK=<expr>[;<expr>...]` logs each expression's bytes every
//! `VICTORY_PEEK_MS` milliseconds (2000), from the title's start on, to watch
//! the title's own state (a flag, a counter) where a hang leaves no other
//! trace. An expression is `<rva>[><offset>...]:<bytes>`, numbers in hex
//! with or without `0x`: the address is the image's base plus `rva`; each
//! `><offset>` reads the pointer at the address so far and adds `offset` to
//! it; then `bytes` (at most 0x400) are read there and logged. Reads go
//! through `ReadProcessMemory` on our own process, so memory that is not
//! mapped reads as an error and never faults. Off unless set.

use windows_sys::Win32::System::Diagnostics::Debug::ReadProcessMemory;
use windows_sys::Win32::System::Threading::GetCurrentProcess;

/// One expression: the offset from the image base, the pointer steps, and
/// how many bytes to log.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Expr {
    rva: u64,
    steps: Vec<u64>,
    bytes: usize,
    text: String,
}

fn number(s: &str) -> Option<u64> {
    let s = s.trim();
    u64::from_str_radix(
        s.strip_prefix("0x")
            .or_else(|| s.strip_prefix("0X"))
            .unwrap_or(s),
        16,
    )
    .ok()
}

/// Parses `VICTORY_PEEK`'s value; expressions that do not parse are left out.
fn parse(value: &str) -> Vec<Expr> {
    value
        .split(';')
        .filter_map(|e| {
            let (path, bytes) = e.trim().rsplit_once(':')?;
            let mut parts = path.split('>');
            let rva = number(parts.next()?)?;
            let steps = parts.map(number).collect::<Option<Vec<_>>>()?;
            let bytes = (number(bytes)? as usize).min(0x400);
            Some(Expr {
                rva,
                steps,
                bytes,
                text: e.trim().to_owned(),
            })
        })
        .collect()
}

fn read(at: u64, out: &mut [u8]) -> bool {
    let mut done = 0usize;
    // SAFETY: our own process; `out` is ours and of that length.
    let ok = unsafe {
        ReadProcessMemory(
            GetCurrentProcess(),
            at as *const _,
            out.as_mut_ptr().cast(),
            out.len(),
            &mut done,
        )
    };
    ok != 0 && done == out.len()
}

/// The address `expr` names in the image at `base` (its pointer steps
/// followed), or the pointer that could not be read.
fn address(base: u64, expr: &Expr) -> Result<u64, u64> {
    let mut at = base.wrapping_add(expr.rva);
    for step in &expr.steps {
        let mut pointer = [0u8; 8];
        if !read(at, &mut pointer) {
            return Err(at);
        }
        at = u64::from_le_bytes(pointer).wrapping_add(*step);
    }
    Ok(at)
}

/// For `VICTORY_WATCH`: the first expression in `value` (peek syntax) and
/// its byte count.
pub(crate) fn parse_one(
    value: &str,
) -> Option<(impl Fn(u64) -> Option<u64> + use<>, usize, String)> {
    let expr = parse(value).into_iter().next()?;
    let (bytes, text) = (expr.bytes, expr.text.clone());
    Some((
        move |base| {
            address(base, &expr)
                .ok()
                .filter(|&at| read(at, &mut [0u8; 1]))
        },
        bytes,
        text,
    ))
}

/// The bytes `expr` names in the image at `base`, as hex, or why not.
fn evaluate(base: u64, expr: &Expr) -> String {
    let at = match address(base, expr) {
        Ok(at) => at,
        Err(at) => return format!("unreadable pointer at {at:#x}"),
    };
    let mut bytes = vec![0u8; expr.bytes];
    if !read(at, &mut bytes) {
        return format!("unreadable {} bytes at {at:#x}", expr.bytes);
    }
    let hex: Vec<String> = bytes
        .chunks(8)
        .map(|c| c.iter().map(|b| format!("{b:02x}")).collect())
        .collect();
    format!("at {at:#x}: {}", hex.join(" "))
}

/// Starts the logging thread for the title's image at `base`, if asked.
pub(crate) fn start(base: usize) {
    let Ok(value) = std::env::var("VICTORY_PEEK") else {
        return;
    };
    let exprs = parse(&value);
    if exprs.is_empty() {
        tracing::warn!(value, "VICTORY_PEEK: no expression parsed");
        return;
    }
    let every = std::env::var("VICTORY_PEEK_MS")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .unwrap_or(2000)
        .max(100);
    let spawned = std::thread::Builder::new()
        .name("victory-peek".into())
        .spawn(move || {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(every));
                for e in &exprs {
                    tracing::info!(expr = %e.text, "peek {}", evaluate(base as u64, e));
                }
            }
        });
    if let Err(e) = spawned {
        tracing::warn!(error = %e, "VICTORY_PEEK: no thread");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expressions_parse_with_steps_and_hex() {
        let e = parse("0x9AE9950>0>28:40; 9ae9958:8 ; bad");
        assert_eq!(e.len(), 2);
        assert_eq!(
            (e[0].rva, e[0].steps.clone(), e[0].bytes),
            (0x9AE9950, vec![0, 0x28], 0x40)
        );
        assert_eq!(
            (e[1].rva, e[1].steps.clone(), e[1].bytes),
            (0x9AE9958, vec![], 8)
        );
    }

    #[test]
    fn our_own_memory_reads_and_bad_memory_does_not_fault() {
        let value: u64 = 0x1122_3344_5566_7788;
        let base = &value as *const u64 as u64;
        let e = Expr {
            rva: 0,
            steps: vec![],
            bytes: 8,
            text: String::new(),
        };
        assert!(evaluate(base, &e).ends_with("8877665544332211"));
        let bad = Expr {
            rva: 0,
            steps: vec![0],
            bytes: 8,
            text: String::new(),
        };
        assert!(evaluate(8, &bad).starts_with("unreadable"));
    }
}
