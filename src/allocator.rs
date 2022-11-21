//! # A Custom Memory Allocator
//!
//! `CustomAllocator` is a custom memory allocator
//!
//! # Example
//!
//! ```
//! use safe_drive::allocator::ALLOCATOR;
//! use std::alloc::{GlobalAlloc, Layout, System};
//!
//! static mut MY_ALLOCATOR: memac::Allocator<memac::buddy::Buddy32M> = memac::Allocator::new();
//! const MEMSIZE_32M: usize = 32 * 1024 * 1024; // 32MiB
//!
//! fn main() {
//!     unsafe {
//!         let layout = Layout::from_size_align(MEMSIZE_32M, memac::ALIGNMENT).unwrap();
//!         let heap_start = System.alloc(layout);
//!
//!         assert!(!heap_start.is_null());
//!
//!         MY_ALLOCATOR.init(heap_start as usize, MEMSIZE_32M);
//!         ALLOCATOR.init(&MY_ALLOCATOR, heap_start as usize, MEMSIZE_32M);
//!     }
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

pub struct CustomAllocator {
    allocator: Option<&'static dyn GlobalAlloc>,
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
            allocator: None,
            heap: (0, 0),
        }
    }

    /// Set a heap memory region to the custom memory allocator.
    /// The allocated memory region will be automatically touched to avoid
    /// dynamic page allocation of demand paging.
    pub unsafe fn init(
        &mut self,
        allocator: &'static dyn GlobalAlloc,
        heap_start: usize,
        size: usize,
    ) {
        // Touch memory.
        let mem = from_raw_parts_mut(heap_start as *mut u8, size);
        for i in (0..size).step_by(4096) {
            write_volatile(&mut mem[i], 0);
        }

        self.allocator = Some(allocator);
        self.heap = (heap_start, size);
    }
}

unsafe impl GlobalAlloc for CustomAllocator {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        if let Some(allocator) = self.allocator {
            let result = allocator.alloc(layout);

            if result.is_null() {
                System.alloc(layout)
            } else {
                result
            }
        } else {
            System.alloc(layout)
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        let addr = ptr as usize;

        if let Some(allocator) = self.allocator {
            if self.heap.contains(addr) {
                allocator.dealloc(ptr, layout)
            } else {
                System.dealloc(ptr, layout)
            }
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
