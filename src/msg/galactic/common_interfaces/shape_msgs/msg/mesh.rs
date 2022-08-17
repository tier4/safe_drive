// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn shape_msgs__msg__Mesh__init(msg: *mut Mesh) -> bool;
    fn shape_msgs__msg__Mesh__fini(msg: *mut Mesh);
    fn shape_msgs__msg__Mesh__are_equal(lhs: *const Mesh, rhs: *const Mesh) -> bool;
    fn shape_msgs__msg__Mesh__Sequence__init(msg: *mut MeshSeqRaw, size: usize) -> bool;
    fn shape_msgs__msg__Mesh__Sequence__fini(msg: *mut MeshSeqRaw);
    fn shape_msgs__msg__Mesh__Sequence__are_equal(
        lhs: *const MeshSeqRaw,
        rhs: *const MeshSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__shape_msgs__msg__Mesh(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct Mesh {
    pub triangles: MeshTriangleSeq<0>,
    pub vertices: geometry_msgs::msg::PointSeq<0>,
}

impl Mesh {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { shape_msgs__msg__Mesh__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for Mesh {
    fn drop(&mut self) {
        unsafe { shape_msgs__msg__Mesh__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct MeshSeqRaw {
    data: *mut Mesh,
    size: usize,
    capacity: usize,
}

/// Sequence of Mesh.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct MeshSeq<const N: usize> {
    data: *mut Mesh,
    size: usize,
    capacity: usize,
}

impl<const N: usize> MeshSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size >= N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: MeshSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { shape_msgs__msg__Mesh__Sequence__init(&mut msg, size) } {
            Some(Self {
                data: msg.data,
                size: msg.size,
                capacity: msg.capacity,
            })
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> &[Mesh] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [Mesh] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }
}

impl<const N: usize> Drop for MeshSeq<N> {
    fn drop(&mut self) {
        let mut msg = MeshSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { shape_msgs__msg__Mesh__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for MeshSeq<N> {}
unsafe impl<const N: usize> Sync for MeshSeq<N> {}

impl TopicMsg for Mesh {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe { rosidl_typesupport_c__get_message_type_support_handle__shape_msgs__msg__Mesh() }
    }
}

impl PartialEq for Mesh {
    fn eq(&self, other: &Self) -> bool {
        unsafe { shape_msgs__msg__Mesh__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for MeshSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = MeshSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = MeshSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            shape_msgs__msg__Mesh__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
