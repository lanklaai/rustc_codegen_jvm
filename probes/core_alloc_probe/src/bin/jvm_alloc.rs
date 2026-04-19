#![feature(alloc_error_handler)]
#![no_std]
#![no_main]

extern crate alloc;

use alloc::{string::String, vec::Vec};
use core::alloc::{GlobalAlloc, Layout};
use core::panic::PanicInfo;
use core::ptr::null_mut;

struct ProbeAlloc;

unsafe impl GlobalAlloc for ProbeAlloc {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        null_mut()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static ALLOC: ProbeAlloc = ProbeAlloc;

#[alloc_error_handler]
fn alloc_error(_layout: Layout) -> ! {
    loop {}
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    let mut values = Vec::new();
    values.push(1);

    let mut text = String::from("x");
    text.push('y');

    (values.len() + text.len()) as i32
}
