#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::too_many_arguments)]

mod galactic;

pub use galactic::*;

#[repr(C)]
#[derive(Debug)]
pub struct Sequence<T> {
    data: *mut T,
    size: std::os::raw::c_ulong,
    capacity: std::os::raw::c_ulong,
}

impl<T> Sequence<T> {
    pub fn as_slice(&self) -> Option<&[T]> {
        if self.data.is_null() {
            None
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as usize) };
            Some(s)
        }
    }

    pub fn as_slice_mut(&mut self) -> Option<&mut [T]> {
        if self.data.is_null() {
            None
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as usize) };
            Some(s)
        }
    }
}

macro_rules! sequence {
    ($ty: ident, $ty_orig:ty, $ty_seq:ty, $init:ident, $fini:ident) => {
        #[repr(C)]
        #[derive(Debug)]
        pub struct $ty($ty_seq);

        impl $ty {
            pub fn new(size: usize) -> Option<Self> {
                let mut msg: $ty_seq = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
                if unsafe { $init(&mut msg, size as u64) } {
                    Some($ty(msg))
                } else {
                    None
                }
            }

            pub fn as_slice(&self) -> Option<&[$ty_orig]> {
                if self.0.data.is_null() {
                    None
                } else {
                    let s =
                        unsafe { std::slice::from_raw_parts(self.0.data, self.0.size as usize) };
                    Some(s)
                }
            }

            pub fn as_slice_mut(&mut self) -> Option<&mut [$ty_orig]> {
                if self.0.data.is_null() {
                    None
                } else {
                    let s = unsafe {
                        std::slice::from_raw_parts_mut(self.0.data, self.0.size as usize)
                    };
                    Some(s)
                }
            }
        }

        impl Drop for $ty {
            fn drop(&mut self) {
                unsafe { $fini(&mut self.0 as *mut _) };
            }
        }
    };
}

sequence!(
    BoolSeq,
    bool,
    rosidl_runtime_c__boolean__Sequence,
    rosidl_runtime_c__boolean__Sequence__init,
    rosidl_runtime_c__boolean__Sequence__fini
);

sequence!(
    F32Seq,
    f32,
    rosidl_runtime_c__float__Sequence,
    rosidl_runtime_c__float__Sequence__init,
    rosidl_runtime_c__float__Sequence__fini
);

sequence!(
    F64Seq,
    f64,
    rosidl_runtime_c__double__Sequence,
    rosidl_runtime_c__double__Sequence__init,
    rosidl_runtime_c__double__Sequence__fini
);

sequence!(
    CharSeq,
    std::os::raw::c_schar,
    rosidl_runtime_c__char__Sequence,
    rosidl_runtime_c__char__Sequence__init,
    rosidl_runtime_c__char__Sequence__fini
);

sequence!(
    OctetSeq,
    u8,
    rosidl_runtime_c__octet__Sequence,
    rosidl_runtime_c__octet__Sequence__init,
    rosidl_runtime_c__octet__Sequence__fini
);

sequence!(
    U8Seq,
    u8,
    rosidl_runtime_c__uint8__Sequence,
    rosidl_runtime_c__uint8__Sequence__init,
    rosidl_runtime_c__uint8__Sequence__fini
);

sequence!(
    I8Seq,
    i8,
    rosidl_runtime_c__int8__Sequence,
    rosidl_runtime_c__int8__Sequence__init,
    rosidl_runtime_c__int8__Sequence__fini
);

sequence!(
    U16Seq,
    u16,
    rosidl_runtime_c__uint16__Sequence,
    rosidl_runtime_c__uint16__Sequence__init,
    rosidl_runtime_c__uint16__Sequence__fini
);

sequence!(
    I16Seq,
    i16,
    rosidl_runtime_c__int16__Sequence,
    rosidl_runtime_c__int16__Sequence__init,
    rosidl_runtime_c__int16__Sequence__fini
);

sequence!(
    U32Seq,
    u32,
    rosidl_runtime_c__uint32__Sequence,
    rosidl_runtime_c__uint32__Sequence__init,
    rosidl_runtime_c__uint32__Sequence__fini
);

sequence!(
    I32Seq,
    i32,
    rosidl_runtime_c__int32__Sequence,
    rosidl_runtime_c__int32__Sequence__init,
    rosidl_runtime_c__int32__Sequence__fini
);

sequence!(
    U64Seq,
    u64,
    rosidl_runtime_c__uint64__Sequence,
    rosidl_runtime_c__uint64__Sequence__init,
    rosidl_runtime_c__uint64__Sequence__fini
);

sequence!(
    I64Seq,
    i64,
    rosidl_runtime_c__int64__Sequence,
    rosidl_runtime_c__int64__Sequence__init,
    rosidl_runtime_c__int64__Sequence__fini
);

sequence!(
    StringSeq,
    rosidl_runtime_c__String,
    rosidl_runtime_c__String__Sequence,
    rosidl_runtime_c__String__Sequence__init,
    rosidl_runtime_c__String__Sequence__fini
);
