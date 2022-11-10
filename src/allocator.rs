//! # A Custom Memory Allocator
//!
//! `CustomAllocator` is a custom memory allocator using the slab allocator.
//!
//! # Example
//!
//! ```
//! use safe_drive::allocator::ALLOCATOR;
//! fn main() {
//!     unsafe { ALLOCATOR.init() };
//! }
//! ```

use crate::{helper::Contains, rcl::size_t};
use std::{
    alloc::{GlobalAlloc, Layout, System},
    mem::size_of,
    os::raw::c_void,
    ptr::{null_mut, write_volatile},
    slice::{from_raw_parts, from_raw_parts_mut},
};

pub use memac::ALIGNMENT;

#[cfg(feature = "memsize_32m")]
const MEMSIZE: usize = 32 * 1024 * 1024;

#[cfg(feature = "memsize_64m")]
const MEMSIZE: usize = 64 * 1024 * 1024;

#[cfg(feature = "memsize_128m")]
const MEMSIZE: usize = 128 * 1024 * 1024;

#[cfg(feature = "memsize_256m")]
const MEMSIZE: usize = 256 * 1024 * 1024;

#[cfg(feature = "memsize_512m")]
const MEMSIZE: usize = 512 * 1024 * 1024;

#[cfg(feature = "memsize_1g")]
const MEMSIZE: usize = 1024 * 1024 * 1024;

#[cfg(feature = "memsize_2g")]
const MEMSIZE: usize = 2 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_4g")]
const MEMSIZE: usize = 4 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_8g")]
const MEMSIZE: usize = 8 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_16g")]
const MEMSIZE: usize = 16 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_32g")]
const MEMSIZE: usize = 32 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_64g")]
const MEMSIZE: usize = 64 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_128g")]
const MEMSIZE: usize = 128 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_256g")]
const MEMSIZE: usize = 256 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_512g")]
const MEMSIZE: usize = 512 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_1t")]
const MEMSIZE: usize = 1024 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_2t")]
const MEMSIZE: usize = 2 * 1024 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_4t")]
const MEMSIZE: usize = 4 * 1024 * 1024 * 1024 * 1024;

#[cfg(feature = "memsize_8t")]
const MEMSIZE: usize = 8 * 1024 * 1024 * 1024 * 1024;

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
    pub unsafe fn init(&mut self) -> bool {
        if let Ok(layout) = Layout::from_size_align(MEMSIZE, memac::ALIGNMENT) {
            let result = System.alloc(layout);
            if result.is_null() {
                false
            } else {
                let start = result as usize;

                // Touch memory.
                let mem = from_raw_parts_mut(result, MEMSIZE);
                for i in (0..MEMSIZE).step_by(4096) {
                    write_volatile(&mut mem[i], 0);
                }

                self.allocator.init(start);
                self.heap = (start, start + MEMSIZE);

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

#[no_mangle]
pub unsafe extern "C" fn allocate(size: size_t, _state: *mut c_void) -> *mut c_void {
    let layout =
        Layout::from_size_align(size as usize + size_of::<usize>(), size_of::<usize>()).unwrap();
    let result = ALLOCATOR.alloc(layout);

    if result.is_null() {
        return null_mut();
    }

    let arr = from_raw_parts_mut(result as *mut usize, 1);
    arr[0] = size as usize;

    let addr = result as usize + size_of::<usize>();
    addr as _
}

#[no_mangle]
pub unsafe extern "C" fn deallocate(pointer: *mut c_void, _state: *mut c_void) {
    if pointer.is_null() {
        return;
    }

    let addr = pointer as usize - size_of::<usize>();

    let arr = from_raw_parts(addr as *const usize, 1);
    let size = arr[0];

    let layout =
        Layout::from_size_align(size as usize + size_of::<usize>(), size_of::<usize>()).unwrap();

    ALLOCATOR.dealloc(addr as _, layout);
}

#[no_mangle]
pub unsafe extern "C" fn reallocate(
    pointer: *mut c_void,
    size: size_t,
    state: *mut c_void,
) -> *mut c_void {
    if pointer.is_null() {
        return allocate(size, state);
    }

    let addr = pointer as usize - size_of::<usize>();

    let arr = from_raw_parts(addr as *const usize, 1);
    let prev_size = arr[0];

    let layout =
        Layout::from_size_align(prev_size as usize + size_of::<usize>(), size_of::<usize>())
            .unwrap();

    let result = ALLOCATOR.realloc(addr as _, layout, size as usize + size_of::<usize>());

    if result.is_null() {
        return null_mut();
    }

    let arr = from_raw_parts_mut(result as *mut usize, 1);
    arr[0] = size as usize;

    let addr = result as usize + size_of::<usize>();
    addr as _
}

#[no_mangle]
pub unsafe extern "C" fn zero_allocate(
    number_of_elements: size_t,
    size_of_element: size_t,
    _state: *mut c_void,
) -> *mut c_void {
    let size = (number_of_elements * size_of_element) as usize;

    let layout = Layout::from_size_align(size + size_of::<usize>(), size_of::<usize>()).unwrap();
    let result = ALLOCATOR.alloc_zeroed(layout);

    if result.is_null() {
        return null_mut();
    }

    let arr = from_raw_parts_mut(result as *mut usize, 1);
    arr[0] = size as usize;

    let addr = result as usize + size_of::<usize>();
    addr as _
}
