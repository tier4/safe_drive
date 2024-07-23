// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn sensor_msgs__msg__FluidPressure__init(msg: *mut FluidPressure) -> bool;
    fn sensor_msgs__msg__FluidPressure__fini(msg: *mut FluidPressure);
    fn sensor_msgs__msg__FluidPressure__are_equal(
        lhs: *const FluidPressure,
        rhs: *const FluidPressure,
    ) -> bool;
    fn sensor_msgs__msg__FluidPressure__Sequence__init(
        msg: *mut FluidPressureSeqRaw,
        size: usize,
    ) -> bool;
    fn sensor_msgs__msg__FluidPressure__Sequence__fini(msg: *mut FluidPressureSeqRaw);
    fn sensor_msgs__msg__FluidPressure__Sequence__are_equal(
        lhs: *const FluidPressureSeqRaw,
        rhs: *const FluidPressureSeqRaw,
    ) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__FluidPressure(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct FluidPressure {
    pub header: std_msgs::msg::Header,
    pub fluid_pressure: f64,
    pub variance: f64,
}

impl FluidPressure {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__FluidPressure__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for FluidPressure {
    fn drop(&mut self) {
        unsafe { sensor_msgs__msg__FluidPressure__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct FluidPressureSeqRaw {
    data: *mut FluidPressure,
    size: size_t,
    capacity: size_t,
}

/// Sequence of FluidPressure.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct FluidPressureSeq<const N: usize> {
    data: *mut FluidPressure,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> FluidPressureSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: FluidPressureSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__FluidPressure__Sequence__init(&mut msg, size) } {
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
        let msg: FluidPressureSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[FluidPressure] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [FluidPressure] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, FluidPressure> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, FluidPressure> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for FluidPressureSeq<N> {
    fn drop(&mut self) {
        let mut msg = FluidPressureSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { sensor_msgs__msg__FluidPressure__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for FluidPressureSeq<N> {}
unsafe impl<const N: usize> Sync for FluidPressureSeq<N> {}

impl TypeSupport for FluidPressure {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__FluidPressure()
        }
    }
}

impl PartialEq for FluidPressure {
    fn eq(&self, other: &Self) -> bool {
        unsafe { sensor_msgs__msg__FluidPressure__are_equal(self, other) }
    }
}

impl<const N: usize> PartialEq for FluidPressureSeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = FluidPressureSeqRaw {
                data: self.data,
                size: self.size,
                capacity: self.capacity,
            };
            let msg2 = FluidPressureSeqRaw {
                data: other.data,
                size: other.size,
                capacity: other.capacity,
            };
            sensor_msgs__msg__FluidPressure__Sequence__are_equal(&msg1, &msg2)
        }
    }
}
