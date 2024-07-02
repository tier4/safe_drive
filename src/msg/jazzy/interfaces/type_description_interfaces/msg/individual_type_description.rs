// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::*;
use super::super::super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn type_description_interfaces__msg__IndividualTypeDescription__init(msg: *mut IndividualTypeDescription) -> bool;
    fn type_description_interfaces__msg__IndividualTypeDescription__fini(msg: *mut IndividualTypeDescription);
    fn type_description_interfaces__msg__IndividualTypeDescription__are_equal(lhs: *const IndividualTypeDescription, rhs: *const IndividualTypeDescription) -> bool;
    fn type_description_interfaces__msg__IndividualTypeDescription__Sequence__init(msg: *mut IndividualTypeDescriptionSeqRaw, size: usize) -> bool;
    fn type_description_interfaces__msg__IndividualTypeDescription__Sequence__fini(msg: *mut IndividualTypeDescriptionSeqRaw);
    fn type_description_interfaces__msg__IndividualTypeDescription__Sequence__are_equal(lhs: *const IndividualTypeDescriptionSeqRaw, rhs: *const IndividualTypeDescriptionSeqRaw) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__type_description_interfaces__msg__IndividualTypeDescription() -> *const rcl::rosidl_message_type_support_t;
}


#[repr(C)]
#[derive(Debug)]
pub struct IndividualTypeDescription {
    pub type_name: crate::msg::RosString<255>,
    pub fields: FieldSeq<0>,
}

impl IndividualTypeDescription {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { type_description_interfaces__msg__IndividualTypeDescription__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for IndividualTypeDescription {
    fn drop(&mut self) {
        unsafe { type_description_interfaces__msg__IndividualTypeDescription__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct IndividualTypeDescriptionSeqRaw {
    data: *mut IndividualTypeDescription,
    size: size_t,
    capacity: size_t,
}

/// Sequence of IndividualTypeDescription.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct IndividualTypeDescriptionSeq<const N: usize> {
    data: *mut IndividualTypeDescription,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> IndividualTypeDescriptionSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: IndividualTypeDescriptionSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { type_description_interfaces__msg__IndividualTypeDescription__Sequence__init(&mut msg, size) } {
            Some(Self {data: msg.data, size: msg.size, capacity: msg.capacity })
        } else {
            None
        }
    }

    pub fn null() -> Self {
        let msg: IndividualTypeDescriptionSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {data: msg.data, size: msg.size, capacity: msg.capacity }
    }

    pub fn as_slice(&self) -> &[IndividualTypeDescription] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [IndividualTypeDescription] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, IndividualTypeDescription> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, IndividualTypeDescription> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for IndividualTypeDescriptionSeq<N> {
    fn drop(&mut self) {
        let mut msg = IndividualTypeDescriptionSeqRaw{data: self.data, size: self.size, capacity: self.capacity};
        unsafe { type_description_interfaces__msg__IndividualTypeDescription__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for IndividualTypeDescriptionSeq<N> {}
unsafe impl<const N: usize> Sync for IndividualTypeDescriptionSeq<N> {}


impl TypeSupport for IndividualTypeDescription {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__type_description_interfaces__msg__IndividualTypeDescription()
        }
    }
}

impl PartialEq for IndividualTypeDescription {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            type_description_interfaces__msg__IndividualTypeDescription__are_equal(self, other)
        }
    }
}

impl<const N: usize> PartialEq for IndividualTypeDescriptionSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = IndividualTypeDescriptionSeqRaw{data: self.data, size: self.size, capacity: self.capacity};
            let msg2 = IndividualTypeDescriptionSeqRaw{data: other.data, size: other.size, capacity: other.capacity};
            type_description_interfaces__msg__IndividualTypeDescription__Sequence__are_equal(&msg1, &msg2)
        }
    }
}

