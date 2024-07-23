// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;
pub const PENDING: u8 = 0; // The goal has yet to be processed by the action server.
pub const ACTIVE: u8 = 1; // The goal is currently being processed by the action server.
pub const PREEMPTED: u8 = 2; // The goal received a cancel request after it started executing
pub const SUCCEEDED: u8 = 3; // The goal was achieved successfully by the action server
pub const ABORTED: u8 = 4; // The goal was aborted during execution by the action server due
pub const REJECTED: u8 = 5; // The goal was rejected by the action server without being processed,
pub const PREEMPTING: u8 = 6; // The goal received a cancel request after it started executing
pub const RECALLING: u8 = 7; // The goal received a cancel request before it started executing, but
pub const RECALLED: u8 = 8; // The goal received a cancel request before it started executing
pub const LOST: u8 = 9; // An action client can determine that a goal is LOST. This should not

extern "C" {
    fn actionlib_msgs__msg__GoalStatus__init(msg: *mut GoalStatus) -> bool;
    fn actionlib_msgs__msg__GoalStatus__fini(msg: *mut GoalStatus);
    fn actionlib_msgs__msg__GoalStatus__are_equal(
        lhs: *const GoalStatus,
        rhs: *const GoalStatus,
    ) -> bool;
    fn actionlib_msgs__msg__GoalStatus__Sequence__init(
        msg: *mut GoalStatusSeqRaw,
        size: usize,
    ) -> bool;
    fn actionlib_msgs__msg__GoalStatus__Sequence__fini(msg: *mut GoalStatusSeqRaw);
    fn actionlib_msgs__msg__GoalStatus__Sequence__are_equal(
        lhs: *const GoalStatusSeqRaw,
        rhs: *const GoalStatusSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__actionlib_msgs__msg__GoalStatus(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct GoalStatus {
    pub goal_id: GoalID,
    pub status: u8,
    pub text: crate::msg::RosString<0>,
}

impl GoalStatus {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { actionlib_msgs__msg__GoalStatus__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for GoalStatus {
    fn drop(&mut self) {
        unsafe { actionlib_msgs__msg__GoalStatus__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct GoalStatusSeqRaw {
    data: *mut GoalStatus,
    size: size_t,
    capacity: size_t,
}

/// Sequence of GoalStatus.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct GoalStatusSeq<const N: usize> {
    data: *mut GoalStatus,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> GoalStatusSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: GoalStatusSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { actionlib_msgs__msg__GoalStatus__Sequence__init(&mut msg, size) } {
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
        let msg: GoalStatusSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[GoalStatus] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [GoalStatus] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, GoalStatus> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, GoalStatus> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for GoalStatusSeq<N> {
    fn drop(&mut self) {
        let mut msg = GoalStatusSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { actionlib_msgs__msg__GoalStatus__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for GoalStatusSeq<N> {}
unsafe impl<const N: usize> Sync for GoalStatusSeq<N> {}

impl TypeSupport for GoalStatus {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__actionlib_msgs__msg__GoalStatus()
        }
    }
}

impl PartialEq for GoalStatus {
    fn eq(&self, other: &Self) -> bool {
        unsafe { actionlib_msgs__msg__GoalStatus__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for GoalStatusSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = GoalStatusSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = GoalStatusSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            actionlib_msgs__msg__GoalStatus__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
