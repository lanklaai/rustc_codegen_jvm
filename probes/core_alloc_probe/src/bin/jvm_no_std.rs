#![no_std]
#![no_main]

use core::panic::PanicInfo;
use core::sync::atomic::{AtomicU32, Ordering};

static STATE: AtomicU32 = AtomicU32::new(0);

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    let previous = STATE.fetch_add(41, Ordering::SeqCst);
    if previous == 0 { 1 } else { 0 }
}
