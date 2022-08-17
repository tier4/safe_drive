// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;
pub const ULTRASOUND: u8 = 0;
pub const INFRARED: u8 = 1;

extern "C" {
    fn sensor_msgs__msg__Range__init(msg: *mut Range) -> bool;
    fn sensor_msgs__msg__Range__fini(msg: *mut Range);
    fn sensor_msgs__msg__Range__are_equal(lhs: *const Range, rhs: *const Range) -> bool;
    fn sensor_msgs__msg__Range__Sequence__init(msg: *mut RangeSeqRaw, size: usize) -> bool;
    fn sensor_msgs__msg__Range__Sequence__fini(msg: *mut RangeSeqRaw);
    fn sensor_msgs__msg__Range__Sequence__are_equal(
        lhs: *const RangeSeqRaw,
        rhs: *const RangeSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__Range(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct Range {
    pub header: std_msgs::msg::Header,
    pub radiation_type: u8,
    pub field_of_view: f32,
    pub min_range: f32,
    pub max_range: f32,
    pub range: f32,
}

impl Range {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__Range__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for Range {
    fn drop(&mut self) {
        unsafe { sensor_msgs__msg__Range__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct RangeSeqRaw {
    data: *mut Range,
    size: usize,
    capacity: usize,
}

/// Sequence of Range.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct RangeSeq<const N: usize> {
    data: *mut Range,
    size: usize,
    capacity: usize,
}

impl<const N: usize> RangeSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size >= N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: RangeSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__Range__Sequence__init(&mut msg, size) } {
            Some(Self {
                data: msg.data,
                size: msg.size,
                capacity: msg.capacity,
            })
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> &[Range] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [Range] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }
}

impl<const N: usize> Drop for RangeSeq<N> {
    fn drop(&mut self) {
        let mut msg = RangeSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { sensor_msgs__msg__Range__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for RangeSeq<N> {}
unsafe impl<const N: usize> Sync for RangeSeq<N> {}

impl TopicMsg for Range {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe { rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__Range() }
    }
}

impl PartialEq for Range {
    fn eq(&self, other: &Self) -> bool {
        unsafe { sensor_msgs__msg__Range__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for RangeSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = RangeSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = RangeSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            sensor_msgs__msg__Range__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
