// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn action_msgs__msg__GoalInfo__init(msg: *mut GoalInfo) -> bool;
    fn action_msgs__msg__GoalInfo__fini(msg: *mut GoalInfo);
    fn action_msgs__msg__GoalInfo__are_equal(lhs: *const GoalInfo, rhs: *const GoalInfo) -> bool;
    fn action_msgs__msg__GoalInfo__Sequence__init(msg: *mut GoalInfoSeqRaw, size: usize) -> bool;
    fn action_msgs__msg__GoalInfo__Sequence__fini(msg: *mut GoalInfoSeqRaw);
    fn action_msgs__msg__GoalInfo__Sequence__are_equal(
        lhs: *const GoalInfoSeqRaw,
        rhs: *const GoalInfoSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__action_msgs__msg__GoalInfo(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct GoalInfo {
    pub goal_id: unique_identifier_msgs::msg::UUID,
    pub stamp: builtin_interfaces::UnsafeTime,
}

impl GoalInfo {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { action_msgs__msg__GoalInfo__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for GoalInfo {
    fn drop(&mut self) {
        unsafe { action_msgs__msg__GoalInfo__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct GoalInfoSeqRaw {
    data: *mut GoalInfo,
    size: size_t,
    capacity: size_t,
}

/// Sequence of GoalInfo.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct GoalInfoSeq<const N: usize> {
    data: *mut GoalInfo,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> GoalInfoSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: GoalInfoSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { action_msgs__msg__GoalInfo__Sequence__init(&mut msg, size) } {
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
        let msg: GoalInfoSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[GoalInfo] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [GoalInfo] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, GoalInfo> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, GoalInfo> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for GoalInfoSeq<N> {
    fn drop(&mut self) {
        let mut msg = GoalInfoSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { action_msgs__msg__GoalInfo__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for GoalInfoSeq<N> {}
unsafe impl<const N: usize> Sync for GoalInfoSeq<N> {}

impl TypeSupport for GoalInfo {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__action_msgs__msg__GoalInfo()
        }
    }
}

impl PartialEq for GoalInfo {
    fn eq(&self, other: &Self) -> bool {
        unsafe { action_msgs__msg__GoalInfo__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for GoalInfoSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = GoalInfoSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = GoalInfoSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            action_msgs__msg__GoalInfo__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
