#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(unused_imports)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::too_many_arguments)]

mod galactic;
pub use galactic::*;

use crate::rcl;
use std::{ffi::CString, fmt::Display, intrinsics::transmute};

pub trait TopicMsg {
    fn type_support() -> *const rcl::rosidl_message_type_support_t;
}

pub trait ServiceMsg {
    type Request;
    type Response;
    fn type_support() -> *const rcl::rosidl_service_type_support_t;
}

// Definition of Sequence -------------------------------------------------------------------------

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

macro_rules! def_sequence {
    ($ty: ident, $ty_orig:ty, $ty_seq:ty, $init:ident, $fini:ident) => {
        /// A sequence of elements.
        /// `N` represents the maximum number of elements.
        /// If `N` is `0`, the sequence is unlimited.
        #[repr(C)]
        #[derive(Debug)]
        pub struct $ty<const N: usize>($ty_seq);

        impl<const N: usize> $ty<N> {
            pub fn new(size: usize) -> Option<Self> {
                if N != 0 && size >= N {
                    // the size exceeds in the maximum number
                    return None;
                }

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

        impl<const N: usize> Drop for $ty<N> {
            fn drop(&mut self) {
                unsafe { $fini(&mut self.0 as *mut _) };
            }
        }

        unsafe impl<const N: usize> Sync for $ty<N> {}
        unsafe impl<const N: usize> Send for $ty<N> {}
    };
}

def_sequence!(
    BoolSeq,
    bool,
    rosidl_runtime_c__boolean__Sequence,
    rosidl_runtime_c__boolean__Sequence__init,
    rosidl_runtime_c__boolean__Sequence__fini
);

def_sequence!(
    F32Seq,
    f32,
    rosidl_runtime_c__float__Sequence,
    rosidl_runtime_c__float__Sequence__init,
    rosidl_runtime_c__float__Sequence__fini
);

def_sequence!(
    F64Seq,
    f64,
    rosidl_runtime_c__double__Sequence,
    rosidl_runtime_c__double__Sequence__init,
    rosidl_runtime_c__double__Sequence__fini
);

def_sequence!(
    U8Seq,
    u8,
    rosidl_runtime_c__uint8__Sequence,
    rosidl_runtime_c__uint8__Sequence__init,
    rosidl_runtime_c__uint8__Sequence__fini
);

def_sequence!(
    I8Seq,
    i8,
    rosidl_runtime_c__int8__Sequence,
    rosidl_runtime_c__int8__Sequence__init,
    rosidl_runtime_c__int8__Sequence__fini
);

def_sequence!(
    U16Seq,
    u16,
    rosidl_runtime_c__uint16__Sequence,
    rosidl_runtime_c__uint16__Sequence__init,
    rosidl_runtime_c__uint16__Sequence__fini
);

def_sequence!(
    I16Seq,
    i16,
    rosidl_runtime_c__int16__Sequence,
    rosidl_runtime_c__int16__Sequence__init,
    rosidl_runtime_c__int16__Sequence__fini
);

def_sequence!(
    U32Seq,
    u32,
    rosidl_runtime_c__uint32__Sequence,
    rosidl_runtime_c__uint32__Sequence__init,
    rosidl_runtime_c__uint32__Sequence__fini
);

def_sequence!(
    I32Seq,
    i32,
    rosidl_runtime_c__int32__Sequence,
    rosidl_runtime_c__int32__Sequence__init,
    rosidl_runtime_c__int32__Sequence__fini
);

def_sequence!(
    U64Seq,
    u64,
    rosidl_runtime_c__uint64__Sequence,
    rosidl_runtime_c__uint64__Sequence__init,
    rosidl_runtime_c__uint64__Sequence__fini
);

def_sequence!(
    I64Seq,
    i64,
    rosidl_runtime_c__int64__Sequence,
    rosidl_runtime_c__int64__Sequence__init,
    rosidl_runtime_c__int64__Sequence__fini
);

// Definition of String ---------------------------------------------------------------------------

/// String.
/// `N` represents the maximum number of characters excluding `\0`.
/// If `N` is `0`, the string is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct RosString<const N: usize>(rosidl_runtime_c__String);

impl<const N: usize> RosString<N> {
    pub fn new(s: &str) -> Option<Self> {
        let mut msg: rosidl_runtime_c__String =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };

        // initialize string
        if unsafe { rosidl_runtime_c__String__init(&mut msg) } {
            if Self::assign_string(&mut msg, s) {
                Some(Self(msg))
            } else {
                None
            }
        } else {
            None
        }
    }

    fn assign_string(msg: &mut rosidl_runtime_c__String, s: &str) -> bool {
        let cs = CString::new(s).unwrap();

        // assign string
        if N == 0 {
            unsafe { rosidl_runtime_c__String__assign(msg, cs.as_ptr()) }
        } else {
            unsafe { rosidl_runtime_c__String__assignn(msg, cs.as_ptr(), N as u64) }
        }
    }

    pub fn assign(&mut self, s: &str) -> bool {
        Self::assign_string(&mut self.0, s)
    }

    pub fn as_slice(&self) -> Option<&[std::os::raw::c_char]> {
        if self.0.data.is_null() {
            None
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.0.data, self.0.size as usize) };
            Some(s)
        }
    }

    pub fn as_slice_mut(&mut self) -> Option<&mut [std::os::raw::c_char]> {
        if self.0.data.is_null() {
            None
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.0.data, self.0.size as usize) };
            Some(s)
        }
    }

    fn get_string(&self) -> String {
        if let Some(s) = self.as_slice() {
            if let Ok(m) = String::from_utf8(s.iter().map(|&c| c as u8).collect()) {
                m
            } else {
                "".to_string()
            }
        } else {
            "".to_string()
        }
    }
}

impl<const N: usize> Drop for RosString<N> {
    fn drop(&mut self) {
        unsafe { rosidl_runtime_c__String__fini(&mut self.0 as *mut _) };
    }
}

impl<const N: usize> Display for RosString<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.get_string();
        write!(f, "{s}")
    }
}

unsafe impl<const N: usize> Sync for RosString<N> {}
unsafe impl<const N: usize> Send for RosString<N> {}

/// Sequence of string.
/// `STRLEN` represents the maximum number of characters excluding `\0`.
/// If `STRLEN` is `0`, the string is unlimited.
/// `M` represents the maximum number of elements in a sequence.
/// If `SEQLEN` is `0`, the sequence is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct RosStringSeq<const STRLEN: usize, const SEQLEN: usize>(
    rosidl_runtime_c__String__Sequence,
);

impl<const STRLEN: usize, const SEQLEN: usize> RosStringSeq<STRLEN, SEQLEN> {
    pub fn new(size: usize) -> Option<Self> {
        if SEQLEN != 0 && size >= SEQLEN {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: rosidl_runtime_c__String__Sequence =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rosidl_runtime_c__String__Sequence__init(&mut msg, size as u64) } {
            Some(Self(msg))
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> Option<&[RosString<STRLEN>]> {
        if self.0.data.is_null() {
            None
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.0.data, self.0.size as usize) };
            let result =
                unsafe { transmute::<&[rosidl_runtime_c__String], &[RosString<STRLEN>]>(s) };
            Some(result)
        }
    }

    pub fn as_slice_mut(&mut self) -> Option<&mut [RosString<STRLEN>]> {
        if self.0.data.is_null() {
            None
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.0.data, self.0.size as usize) };
            let result = unsafe {
                transmute::<&mut [rosidl_runtime_c__String], &mut [RosString<STRLEN>]>(s)
            };
            Some(result)
        }
    }
}

impl<const STRLEN: usize, const SEQLEN: usize> Drop for RosStringSeq<STRLEN, SEQLEN> {
    fn drop(&mut self) {
        unsafe { rosidl_runtime_c__String__Sequence__fini(&mut self.0 as *mut _) };
    }
}

unsafe impl<const STRLEN: usize, const SEQLEN: usize> Sync for RosStringSeq<STRLEN, SEQLEN> {}
unsafe impl<const STRLEN: usize, const SEQLEN: usize> Send for RosStringSeq<STRLEN, SEQLEN> {}

// Definition of builtin_interfaces ---------------------------------------------------------------

pub mod builtin_interfaces {
    use super::*;

    impl TopicMsg for builtin_interfaces__msg__Duration {
        fn type_support() -> *const rcl::rosidl_message_type_support_t {
            unsafe {
                rosidl_typesupport_c__get_message_type_support_handle__builtin_interfaces__msg__Duration()
            }
        }
    }

    def_sequence!(
        DurationSeq,
        builtin_interfaces__msg__Duration,
        builtin_interfaces__msg__Duration__Sequence,
        builtin_interfaces__msg__Duration__Sequence__init,
        builtin_interfaces__msg__Duration__Sequence__fini
    );

    impl TopicMsg for builtin_interfaces__msg__Time {
        fn type_support() -> *const rcl::rosidl_message_type_support_t {
            unsafe {
                rosidl_typesupport_c__get_message_type_support_handle__builtin_interfaces__msg__Time(
                )
            }
        }
    }

    def_sequence!(
        TimeSeq,
        builtin_interfaces__msg__Time,
        builtin_interfaces__msg__Time__Sequence,
        builtin_interfaces__msg__Time__Sequence__init,
        builtin_interfaces__msg__Time__Sequence__fini
    );
}

// Tests ------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_c() {
        let mut msg: rosidl_runtime_c__String =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };

        unsafe {
            rosidl_runtime_c__String__init(&mut msg);
            rosidl_runtime_c__String__assignn(&mut msg, b"Hello, World!\0".as_ptr() as _, 3);
            rosidl_runtime_c__String__fini(&mut msg);
        }

        println!("{:#?}", msg);
    }

    #[test]
    fn test_string_rs() {
        let mut str_seq = RosStringSeq::<0, 0>::new(5).unwrap();
        let s = str_seq.as_slice_mut().unwrap();
        for (i, rosstr) in s.iter_mut().enumerate() {
            let msg = format!("RosString::Assign: i = {i}");
            rosstr.assign(&msg);
        }

        for (i, rosstr) in s.iter().enumerate() {
            let m = rosstr.as_slice().unwrap();
            let m = String::from_utf8(m.iter().map(|&c| c as u8).collect()).unwrap();
            let msg = format!("RosString::Assign: i = {i}");
            println!("{m}");
            assert_eq!(msg, m);
        }
    }
}
