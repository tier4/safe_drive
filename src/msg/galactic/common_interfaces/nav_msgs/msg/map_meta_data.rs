// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn nav_msgs__msg__MapMetaData__init(msg: *mut MapMetaData) -> bool;
    fn nav_msgs__msg__MapMetaData__fini(msg: *mut MapMetaData);
    fn nav_msgs__msg__MapMetaData__are_equal(
        lhs: *const MapMetaData,
        rhs: *const MapMetaData,
    ) -> bool;
    fn nav_msgs__msg__MapMetaData__Sequence__init(msg: *mut MapMetaDataSeqRaw, size: usize)
        -> bool;
    fn nav_msgs__msg__MapMetaData__Sequence__fini(msg: *mut MapMetaDataSeqRaw);
    fn nav_msgs__msg__MapMetaData__Sequence__are_equal(
        lhs: *const MapMetaDataSeqRaw,
        rhs: *const MapMetaDataSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__nav_msgs__msg__MapMetaData(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct MapMetaData {
    pub map_load_time: builtin_interfaces::UnsafeTime,
    pub resolution: f32,
    pub width: u32,
    pub height: u32,
    pub origin: geometry_msgs::msg::Pose,
}

impl MapMetaData {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { nav_msgs__msg__MapMetaData__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for MapMetaData {
    fn drop(&mut self) {
        unsafe { nav_msgs__msg__MapMetaData__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct MapMetaDataSeqRaw {
    data: *mut MapMetaData,
    size: usize,
    capacity: usize,
}

/// Sequence of MapMetaData.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct MapMetaDataSeq<const N: usize> {
    data: *mut MapMetaData,
    size: usize,
    capacity: usize,
}

impl<const N: usize> MapMetaDataSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size >= N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: MapMetaDataSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { nav_msgs__msg__MapMetaData__Sequence__init(&mut msg, size) } {
            Some(Self {
                data: msg.data,
                size: msg.size,
                capacity: msg.capacity,
            })
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> &[MapMetaData] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [MapMetaData] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }
}

impl<const N: usize> Drop for MapMetaDataSeq<N> {
    fn drop(&mut self) {
        let mut msg = MapMetaDataSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { nav_msgs__msg__MapMetaData__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for MapMetaDataSeq<N> {}
unsafe impl<const N: usize> Sync for MapMetaDataSeq<N> {}

impl TopicMsg for MapMetaData {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__nav_msgs__msg__MapMetaData()
        }
    }
}

impl PartialEq for MapMetaData {
    fn eq(&self, other: &Self) -> bool {
        unsafe { nav_msgs__msg__MapMetaData__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for MapMetaDataSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = MapMetaDataSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = MapMetaDataSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            nav_msgs__msg__MapMetaData__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
