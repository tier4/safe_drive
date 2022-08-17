// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn trajectory_msgs__msg__MultiDOFJointTrajectory__init(
        msg: *mut MultiDOFJointTrajectory,
    ) -> bool;
    fn trajectory_msgs__msg__MultiDOFJointTrajectory__fini(msg: *mut MultiDOFJointTrajectory);
    fn trajectory_msgs__msg__MultiDOFJointTrajectory__are_equal(
        lhs: *const MultiDOFJointTrajectory,
        rhs: *const MultiDOFJointTrajectory,
    ) -> bool;
    fn trajectory_msgs__msg__MultiDOFJointTrajectory__Sequence__init(
        msg: *mut MultiDOFJointTrajectorySeqRaw,
        size: usize,
    ) -> bool;
    fn trajectory_msgs__msg__MultiDOFJointTrajectory__Sequence__fini(
        msg: *mut MultiDOFJointTrajectorySeqRaw,
    );
    fn trajectory_msgs__msg__MultiDOFJointTrajectory__Sequence__are_equal(
        lhs: *const MultiDOFJointTrajectorySeqRaw,
        rhs: *const MultiDOFJointTrajectorySeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__trajectory_msgs__msg__MultiDOFJointTrajectory(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct MultiDOFJointTrajectory {
    pub header: std_msgs::msg::Header,
    pub joint_names: crate::msg::RosStringSeq<0, 0>,
    pub points: MultiDOFJointTrajectoryPointSeq<0>,
}

impl MultiDOFJointTrajectory {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { trajectory_msgs__msg__MultiDOFJointTrajectory__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for MultiDOFJointTrajectory {
    fn drop(&mut self) {
        unsafe { trajectory_msgs__msg__MultiDOFJointTrajectory__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct MultiDOFJointTrajectorySeqRaw {
    data: *mut MultiDOFJointTrajectory,
    size: usize,
    capacity: usize,
}

/// Sequence of MultiDOFJointTrajectory.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct MultiDOFJointTrajectorySeq<const N: usize> {
    data: *mut MultiDOFJointTrajectory,
    size: usize,
    capacity: usize,
}

impl<const N: usize> MultiDOFJointTrajectorySeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size >= N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: MultiDOFJointTrajectorySeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { trajectory_msgs__msg__MultiDOFJointTrajectory__Sequence__init(&mut msg, size) }
        {
            Some(Self {
                data: msg.data,
                size: msg.size,
                capacity: msg.capacity,
            })
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> &[MultiDOFJointTrajectory] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [MultiDOFJointTrajectory] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }
}

impl<const N: usize> Drop for MultiDOFJointTrajectorySeq<N> {
    fn drop(&mut self) {
        let mut msg = MultiDOFJointTrajectorySeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { trajectory_msgs__msg__MultiDOFJointTrajectory__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for MultiDOFJointTrajectorySeq<N> {}
unsafe impl<const N: usize> Sync for MultiDOFJointTrajectorySeq<N> {}

impl TopicMsg for MultiDOFJointTrajectory {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__trajectory_msgs__msg__MultiDOFJointTrajectory()
        }
    }
}

impl PartialEq for MultiDOFJointTrajectory {
    fn eq(&self, other: &Self) -> bool {
        unsafe { trajectory_msgs__msg__MultiDOFJointTrajectory__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for MultiDOFJointTrajectorySeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = MultiDOFJointTrajectorySeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = MultiDOFJointTrajectorySeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            trajectory_msgs__msg__MultiDOFJointTrajectory__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
