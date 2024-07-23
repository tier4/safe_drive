// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn geometry_msgs__msg__PointStamped__init(msg: *mut PointStamped) -> bool;
    fn geometry_msgs__msg__PointStamped__fini(msg: *mut PointStamped);
    fn geometry_msgs__msg__PointStamped__are_equal(
        lhs: *const PointStamped,
        rhs: *const PointStamped,
    ) -> bool;
    fn geometry_msgs__msg__PointStamped__Sequence__init(
        msg: *mut PointStampedSeqRaw,
        size: usize,
    ) -> bool;
    fn geometry_msgs__msg__PointStamped__Sequence__fini(msg: *mut PointStampedSeqRaw);
    fn geometry_msgs__msg__PointStamped__Sequence__are_equal(
        lhs: *const PointStampedSeqRaw,
        rhs: *const PointStampedSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__geometry_msgs__msg__PointStamped(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct PointStamped {
    pub header: std_msgs::msg::Header,
    pub point: Point,
}

impl PointStamped {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { geometry_msgs__msg__PointStamped__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for PointStamped {
    fn drop(&mut self) {
        unsafe { geometry_msgs__msg__PointStamped__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct PointStampedSeqRaw {
    data: *mut PointStamped,
    size: usize,
    capacity: usize,
}

/// Sequence of PointStamped.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct PointStampedSeq<const N: usize> {
    data: *mut PointStamped,
    size: usize,
    capacity: usize,
}

impl<const N: usize> PointStampedSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: PointStampedSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { geometry_msgs__msg__PointStamped__Sequence__init(&mut msg, size) } {
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
        let msg: PointStampedSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[PointStamped] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [PointStamped] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, PointStamped> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, PointStamped> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for PointStampedSeq<N> {
    fn drop(&mut self) {
        let mut msg = PointStampedSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { geometry_msgs__msg__PointStamped__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for PointStampedSeq<N> {}
unsafe impl<const N: usize> Sync for PointStampedSeq<N> {}

impl TypeSupport for PointStamped {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__geometry_msgs__msg__PointStamped(
            )
        }
    }
}

impl PartialEq for PointStamped {
    fn eq(&self, other: &Self) -> bool {
        unsafe { geometry_msgs__msg__PointStamped__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for PointStampedSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = PointStampedSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = PointStampedSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            geometry_msgs__msg__PointStamped__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
