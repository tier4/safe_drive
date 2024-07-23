// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn sensor_msgs__msg__ChannelFloat32__init(msg: *mut ChannelFloat32) -> bool;
    fn sensor_msgs__msg__ChannelFloat32__fini(msg: *mut ChannelFloat32);
    fn sensor_msgs__msg__ChannelFloat32__are_equal(
        lhs: *const ChannelFloat32,
        rhs: *const ChannelFloat32,
    ) -> bool;
    fn sensor_msgs__msg__ChannelFloat32__Sequence__init(
        msg: *mut ChannelFloat32SeqRaw,
        size: usize,
    ) -> bool;
    fn sensor_msgs__msg__ChannelFloat32__Sequence__fini(msg: *mut ChannelFloat32SeqRaw);
    fn sensor_msgs__msg__ChannelFloat32__Sequence__are_equal(
        lhs: *const ChannelFloat32SeqRaw,
        rhs: *const ChannelFloat32SeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__ChannelFloat32(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct ChannelFloat32 {
    pub name: crate::msg::RosString<0>,
    pub values: crate::msg::F32Seq<0>,
}

impl ChannelFloat32 {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__ChannelFloat32__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for ChannelFloat32 {
    fn drop(&mut self) {
        unsafe { sensor_msgs__msg__ChannelFloat32__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct ChannelFloat32SeqRaw {
    data: *mut ChannelFloat32,
    size: usize,
    capacity: usize,
}

/// Sequence of ChannelFloat32.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct ChannelFloat32Seq<const N: usize> {
    data: *mut ChannelFloat32,
    size: usize,
    capacity: usize,
}

impl<const N: usize> ChannelFloat32Seq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: ChannelFloat32SeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__ChannelFloat32__Sequence__init(&mut msg, size) } {
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
        let msg: ChannelFloat32SeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[ChannelFloat32] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [ChannelFloat32] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, ChannelFloat32> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, ChannelFloat32> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for ChannelFloat32Seq<N> {
    fn drop(&mut self) {
        let mut msg = ChannelFloat32SeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { sensor_msgs__msg__ChannelFloat32__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for ChannelFloat32Seq<N> {}
unsafe impl<const N: usize> Sync for ChannelFloat32Seq<N> {}

impl TypeSupport for ChannelFloat32 {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__ChannelFloat32(
            )
        }
    }
}

impl PartialEq for ChannelFloat32 {
    fn eq(&self, other: &Self) -> bool {
        unsafe { sensor_msgs__msg__ChannelFloat32__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for ChannelFloat32Seq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = ChannelFloat32SeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = ChannelFloat32SeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            sensor_msgs__msg__ChannelFloat32__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
