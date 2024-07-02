// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::*;
use super::super::super::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn sensor_msgs__msg__RelativeHumidity__init(msg: *mut RelativeHumidity) -> bool;
    fn sensor_msgs__msg__RelativeHumidity__fini(msg: *mut RelativeHumidity);
    fn sensor_msgs__msg__RelativeHumidity__are_equal(lhs: *const RelativeHumidity, rhs: *const RelativeHumidity) -> bool;
    fn sensor_msgs__msg__RelativeHumidity__Sequence__init(msg: *mut RelativeHumiditySeqRaw, size: usize) -> bool;
    fn sensor_msgs__msg__RelativeHumidity__Sequence__fini(msg: *mut RelativeHumiditySeqRaw);
    fn sensor_msgs__msg__RelativeHumidity__Sequence__are_equal(lhs: *const RelativeHumiditySeqRaw, rhs: *const RelativeHumiditySeqRaw) -> bool;
    fn rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__RelativeHumidity() -> *const rcl::rosidl_message_type_support_t;
}


#[repr(C)]
#[derive(Debug)]
pub struct RelativeHumidity {
    pub header: std_msgs::msg::Header,
    pub relative_humidity: f64,
    pub variance: f64,
}

impl RelativeHumidity {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__RelativeHumidity__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for RelativeHumidity {
    fn drop(&mut self) {
        unsafe { sensor_msgs__msg__RelativeHumidity__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct RelativeHumiditySeqRaw {
    data: *mut RelativeHumidity,
    size: size_t,
    capacity: size_t,
}

/// Sequence of RelativeHumidity.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct RelativeHumiditySeq<const N: usize> {
    data: *mut RelativeHumidity,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> RelativeHumiditySeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: RelativeHumiditySeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { sensor_msgs__msg__RelativeHumidity__Sequence__init(&mut msg, size) } {
            Some(Self {data: msg.data, size: msg.size, capacity: msg.capacity })
        } else {
            None
        }
    }

    pub fn null() -> Self {
        let msg: RelativeHumiditySeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {data: msg.data, size: msg.size, capacity: msg.capacity }
    }

    pub fn as_slice(&self) -> &[RelativeHumidity] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [RelativeHumidity] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RelativeHumidity> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, RelativeHumidity> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for RelativeHumiditySeq<N> {
    fn drop(&mut self) {
        let mut msg = RelativeHumiditySeqRaw{data: self.data, size: self.size, capacity: self.capacity};
        unsafe { sensor_msgs__msg__RelativeHumidity__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for RelativeHumiditySeq<N> {}
unsafe impl<const N: usize> Sync for RelativeHumiditySeq<N> {}


impl TypeSupport for RelativeHumidity {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__sensor_msgs__msg__RelativeHumidity()
        }
    }
}

impl PartialEq for RelativeHumidity {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            sensor_msgs__msg__RelativeHumidity__are_equal(self, other)
        }
    }
}

impl<const N: usize> PartialEq for RelativeHumiditySeq<N> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let msg1 = RelativeHumiditySeqRaw{data: self.data, size: self.size, capacity: self.capacity};
            let msg2 = RelativeHumiditySeqRaw{data: other.data, size: other.size, capacity: other.capacity};
            sensor_msgs__msg__RelativeHumidity__Sequence__are_equal(&msg1, &msg2)
        }
    }
}

