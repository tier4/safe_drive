// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;
pub const BOX: u8 = 1;
pub const SPHERE: u8 = 2;
pub const CYLINDER: u8 = 3;
pub const CONE: u8 = 4;
pub const PRISM: u8 = 5;
pub const BOX_X: u8 = 0;
pub const BOX_Y: u8 = 1;
pub const BOX_Z: u8 = 2;
pub const SPHERE_RADIUS: u8 = 0;
pub const CYLINDER_HEIGHT: u8 = 0;
pub const CYLINDER_RADIUS: u8 = 1;
pub const CONE_HEIGHT: u8 = 0;
pub const CONE_RADIUS: u8 = 1;
pub const PRISM_HEIGHT: u8 = 0;

extern "C" {
    fn shape_msgs__msg__SolidPrimitive__init(msg: *mut SolidPrimitive) -> bool;
    fn shape_msgs__msg__SolidPrimitive__fini(msg: *mut SolidPrimitive);
    fn shape_msgs__msg__SolidPrimitive__are_equal(
        lhs: *const SolidPrimitive,
        rhs: *const SolidPrimitive,
    ) -> bool;
    fn shape_msgs__msg__SolidPrimitive__Sequence__init(
        msg: *mut SolidPrimitiveSeqRaw,
        size: usize,
    ) -> bool;
    fn shape_msgs__msg__SolidPrimitive__Sequence__fini(msg: *mut SolidPrimitiveSeqRaw);
    fn shape_msgs__msg__SolidPrimitive__Sequence__are_equal(
        lhs: *const SolidPrimitiveSeqRaw,
        rhs: *const SolidPrimitiveSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__shape_msgs__msg__SolidPrimitive(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct SolidPrimitive {
    pub type_: u8,
    pub dimensions: crate::msg::F64Seq<3>,
    pub polygon: geometry_msgs::msg::Polygon,
}

impl SolidPrimitive {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { shape_msgs__msg__SolidPrimitive__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for SolidPrimitive {
    fn drop(&mut self) {
        unsafe { shape_msgs__msg__SolidPrimitive__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct SolidPrimitiveSeqRaw {
    data: *mut SolidPrimitive,
    size: usize,
    capacity: usize,
}

/// Sequence of SolidPrimitive.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct SolidPrimitiveSeq<const N: usize> {
    data: *mut SolidPrimitive,
    size: usize,
    capacity: usize,
}

impl<const N: usize> SolidPrimitiveSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: SolidPrimitiveSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { shape_msgs__msg__SolidPrimitive__Sequence__init(&mut msg, size) } {
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
        let msg: SolidPrimitiveSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[SolidPrimitive] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [SolidPrimitive] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, SolidPrimitive> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, SolidPrimitive> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for SolidPrimitiveSeq<N> {
    fn drop(&mut self) {
        let mut msg = SolidPrimitiveSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { shape_msgs__msg__SolidPrimitive__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for SolidPrimitiveSeq<N> {}
unsafe impl<const N: usize> Sync for SolidPrimitiveSeq<N> {}

impl TypeSupport for SolidPrimitive {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__shape_msgs__msg__SolidPrimitive()
        }
    }
}

impl PartialEq for SolidPrimitive {
    fn eq(&self, other: &Self) -> bool {
        unsafe { shape_msgs__msg__SolidPrimitive__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for SolidPrimitiveSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = SolidPrimitiveSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = SolidPrimitiveSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            shape_msgs__msg__SolidPrimitive__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
