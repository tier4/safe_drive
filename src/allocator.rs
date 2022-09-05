//! # A Custom Memory Allocator
//!
//! `CustomAllocator` is a custom memory allocator using the slab allocator.
//!
//! # Example
//!
//! ```
//! use safe_drive::allocator::ALLOCATOR;
//! fn main() {
//!     unsafe { ALLOCATOR.init(128) }; // 32 * 64KiB = 8MiB
//! }
//! ```

use std::{
    alloc::{GlobalAlloc, Layout, System},
    ptr::write_volatile,
    slice::from_raw_parts_mut,
};

use crate::helper::Contains;

pub use memac::ALIGNMENT;

pub struct CustomAllocator {
    allocator: memac::Allocator,
    heap: (usize, usize),
}

#[global_allocator]
pub static mut ALLOCATOR: CustomAllocator = CustomAllocator::new();

impl Contains for (usize, usize) {
    type T = usize;
    fn contains(&self, val: Self::T) -> bool {
        (self.0..self.1).contains(&val)
    }
}

impl CustomAllocator {
    const fn new() -> Self {
        Self {
            allocator: memac::Allocator::new(),
            heap: (0, 0),
        }
    }

    /// Set a heap memory region to the custom memory allocator.
    /// `pages` is a page size to be used by the allocator.
    /// So, `pages * ALIGNMENT` bytes will be allocated, and
    /// `ALIGNMENT` is 64KiB.
    ///
    /// The allocated memory region will be automatically touched to avoid
    /// dynamic page allocation of demand paging.
    pub unsafe fn init(&mut self, pages: usize) -> bool {
        let size = pages * ALIGNMENT;
        if let Ok(layout) = Layout::from_size_align(size, memac::ALIGNMENT) {
            let result = System.alloc(layout);
            if result.is_null() {
                false
            } else {
                let start = result as usize;

                // Touch memory.
                let mem = from_raw_parts_mut(result, size);
                for i in (0..size).step_by(4096) {
                    write_volatile(&mut mem[i], 0);
                }

                self.heap = (start, start + size);
                true
            }
        } else {
            false
        }
    }
}

unsafe impl GlobalAlloc for CustomAllocator {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        let result = self.allocator.alloc(layout);

        if result.is_null() {
            System.alloc(layout)
        } else {
            result
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        let addr = ptr as usize;
        if self.heap.contains(addr) {
            self.allocator.dealloc(ptr, layout)
        } else {
            System.dealloc(ptr, layout)
        }
    }
}
