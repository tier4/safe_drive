// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn std_msgs__msg__Int16MultiArray__init(msg: *mut Int16MultiArray) -> bool;
    fn std_msgs__msg__Int16MultiArray__fini(msg: *mut Int16MultiArray);
    fn std_msgs__msg__Int16MultiArray__are_equal(
        lhs: *const Int16MultiArray,
        rhs: *const Int16MultiArray,
    ) -> bool;
    fn std_msgs__msg__Int16MultiArray__Sequence__init(
        msg: *mut Int16MultiArraySeqRaw,
        size: usize,
    ) -> bool;
    fn std_msgs__msg__Int16MultiArray__Sequence__fini(msg: *mut Int16MultiArraySeqRaw);
    fn std_msgs__msg__Int16MultiArray__Sequence__are_equal(
        lhs: *const Int16MultiArraySeqRaw,
        rhs: *const Int16MultiArraySeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__std_msgs__msg__Int16MultiArray(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct Int16MultiArray {
    pub layout: MultiArrayLayout,
    pub data: crate::msg::I16Seq<0>,
}

impl Int16MultiArray {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { std_msgs__msg__Int16MultiArray__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for Int16MultiArray {
    fn drop(&mut self) {
        unsafe { std_msgs__msg__Int16MultiArray__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct Int16MultiArraySeqRaw {
    data: *mut Int16MultiArray,
    size: usize,
    capacity: usize,
}

/// Sequence of Int16MultiArray.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct Int16MultiArraySeq<const N: usize> {
    data: *mut Int16MultiArray,
    size: usize,
    capacity: usize,
}

impl<const N: usize> Int16MultiArraySeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size >= N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: Int16MultiArraySeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { std_msgs__msg__Int16MultiArray__Sequence__init(&mut msg, size) } {
            Some(Self {
                data: msg.data,
                size: msg.size,
                capacity: msg.capacity,
            })
        } else {
            None
        }
    }

    pub fn null() -> Self {
        let msg: Int16MultiArraySeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[Int16MultiArray] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [Int16MultiArray] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Int16MultiArray> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, Int16MultiArray> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for Int16MultiArraySeq<N> {
    fn drop(&mut self) {
        let mut msg = Int16MultiArraySeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { std_msgs__msg__Int16MultiArray__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for Int16MultiArraySeq<N> {}
unsafe impl<const N: usize> Sync for Int16MultiArraySeq<N> {}

impl TypeSupport for Int16MultiArray {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__std_msgs__msg__Int16MultiArray()
        }
    }
}

impl PartialEq for Int16MultiArray {
    fn eq(&self, other: &Self) -> bool {
        unsafe { std_msgs__msg__Int16MultiArray__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for Int16MultiArraySeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = Int16MultiArraySeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = Int16MultiArraySeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            std_msgs__msg__Int16MultiArray__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
