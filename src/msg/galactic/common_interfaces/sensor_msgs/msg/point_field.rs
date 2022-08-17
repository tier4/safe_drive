// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn sensor_msgs__msg__PointField__init(msg: *mut PointField) -> bool;
    fn sensor_msgs__msg__PointField__fini(msg: *mut PointField);
    fn sensor_msgs__msg__PointField__are_equal(
        lhs: *const PointField,
        rhs: *const PointField,
    ) -> bool;
    fn sensor_msgs__msg__PointField__Sequence__init(
        msg: *mut PointFieldSeqRaw,
        size: usize,
    ) -> bool;
    fn sensor_msgs__msg__PointField__Sequence__fini(msg: *mut PointFieldSeqRaw);
    fn sensor_msgs__msg__PointField__Sequence__are_equal(
        lhs: *const PointFieldSeqRaw,
        rhs: *const PointFieldSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__PointField(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct PointField {
    pub INT8: u8,
    pub UINT8: u8,
    pub INT16: u8,
    pub UINT16: u8,
    pub INT32: u8,
    pub UINT32: u8,
    pub FLOAT32: u8,
    pub FLOAT64: u8,
    pub name: crate::msg::RosString<0>,
    pub offset: u32,
    pub datatype: u8,
    pub count: u32,
}

impl PointField {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__PointField__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for PointField {
    fn drop(&mut self) {
        unsafe { sensor_msgs__msg__PointField__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct PointFieldSeqRaw {
    data: *mut PointField,
    size: usize,
    capacity: usize,
}

/// Sequence of PointField.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct PointFieldSeq<const N: usize> {
    data: *mut PointField,
    size: usize,
    capacity: usize,
}

impl<const N: usize> PointFieldSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size >= N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: PointFieldSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__PointField__Sequence__init(&mut msg, size) } {
            Some(Self {
                data: msg.data,
                size: msg.size,
                capacity: msg.capacity,
            })
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> &[PointField] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [PointField] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }
}

impl<const N: usize> Drop for PointFieldSeq<N> {
    fn drop(&mut self) {
        let mut msg = PointFieldSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { sensor_msgs__msg__PointField__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for PointFieldSeq<N> {}
unsafe impl<const N: usize> Sync for PointFieldSeq<N> {}

impl TopicMsg for PointField {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__PointField()
        }
    }
}

impl PartialEq for PointField {
    fn eq(&self, other: &Self) -> bool {
        unsafe { sensor_msgs__msg__PointField__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for PointFieldSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = PointFieldSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = PointFieldSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            sensor_msgs__msg__PointField__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
