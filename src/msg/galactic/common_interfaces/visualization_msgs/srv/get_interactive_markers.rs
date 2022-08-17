// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::super::*;
use crate::msg::common_interfaces::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn visualization_msgs__srv__GetInteractiveMarkers_Request__init(
        msg: *mut GetInteractiveMarkersRequest,
    ) -> bool;
    fn visualization_msgs__srv__GetInteractiveMarkers_Request__fini(
        msg: *mut GetInteractiveMarkersRequest,
    );
    fn visualization_msgs__srv__GetInteractiveMarkers_Request__Sequence__init(
        msg: *mut GetInteractiveMarkersRequestSeqRaw,
        size: usize,
    ) -> bool;
    fn visualization_msgs__srv__GetInteractiveMarkers_Request__Sequence__fini(
        msg: *mut GetInteractiveMarkersRequestSeqRaw,
    );
    fn visualization_msgs__srv__GetInteractiveMarkers_Response__init(
        msg: *mut GetInteractiveMarkersResponse,
    ) -> bool;
    fn visualization_msgs__srv__GetInteractiveMarkers_Response__fini(
        msg: *mut GetInteractiveMarkersResponse,
    );
    fn visualization_msgs__srv__GetInteractiveMarkers_Response__Sequence__init(
        msg: *mut GetInteractiveMarkersResponseSeqRaw,
        size: usize,
    ) -> bool;
    fn visualization_msgs__srv__GetInteractiveMarkers_Response__Sequence__fini(
        msg: *mut GetInteractiveMarkersResponseSeqRaw,
    );
    fn rosidl_typesupport_c__get_service_type_support_handle__visualization_msgs__srv__GetInteractiveMarkers(
    ) -> *const rcl::rosidl_service_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct GetInteractiveMarkersRequest {
    _unused: u8,
}

#[repr(C)]
#[derive(Debug)]
pub struct GetInteractiveMarkersResponse {
    pub sequence_number: u64,
    pub markers: InteractiveMarkerSeq<0>,
}

impl GetInteractiveMarkersRequest {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { visualization_msgs__srv__GetInteractiveMarkers_Request__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for GetInteractiveMarkersRequest {
    fn drop(&mut self) {
        unsafe { visualization_msgs__srv__GetInteractiveMarkers_Request__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct GetInteractiveMarkersRequestSeqRaw {
    data: *mut GetInteractiveMarkersRequest,
    size: usize,
    capacity: usize,
}

/// Sequence of GetInteractiveMarkersRequest.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct GetInteractiveMarkersRequestSeq<const N: usize> {
    data: *mut GetInteractiveMarkersRequest,
    size: usize,
    capacity: usize,
}

impl<const N: usize> GetInteractiveMarkersRequestSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size >= N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: GetInteractiveMarkersRequestSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe {
            visualization_msgs__srv__GetInteractiveMarkers_Request__Sequence__init(&mut msg, size)
        } {
            Some(Self {
                data: msg.data,
                size: msg.size,
                capacity: msg.capacity,
            })
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> &[GetInteractiveMarkersRequest] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [GetInteractiveMarkersRequest] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }
}

impl<const N: usize> Drop for GetInteractiveMarkersRequestSeq<N> {
    fn drop(&mut self) {
        let mut msg = GetInteractiveMarkersRequestSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { visualization_msgs__srv__GetInteractiveMarkers_Request__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for GetInteractiveMarkersRequestSeq<N> {}
unsafe impl<const N: usize> Sync for GetInteractiveMarkersRequestSeq<N> {}

impl GetInteractiveMarkersResponse {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { visualization_msgs__srv__GetInteractiveMarkers_Response__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for GetInteractiveMarkersResponse {
    fn drop(&mut self) {
        unsafe { visualization_msgs__srv__GetInteractiveMarkers_Response__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct GetInteractiveMarkersResponseSeqRaw {
    data: *mut GetInteractiveMarkersResponse,
    size: usize,
    capacity: usize,
}

/// Sequence of GetInteractiveMarkersResponse.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct GetInteractiveMarkersResponseSeq<const N: usize> {
    data: *mut GetInteractiveMarkersResponse,
    size: usize,
    capacity: usize,
}

impl<const N: usize> GetInteractiveMarkersResponseSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size >= N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: GetInteractiveMarkersResponseSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe {
            visualization_msgs__srv__GetInteractiveMarkers_Response__Sequence__init(&mut msg, size)
        } {
            Some(Self {
                data: msg.data,
                size: msg.size,
                capacity: msg.capacity,
            })
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> &[GetInteractiveMarkersResponse] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [GetInteractiveMarkersResponse] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size) };
            s
        }
    }
}

impl<const N: usize> Drop for GetInteractiveMarkersResponseSeq<N> {
    fn drop(&mut self) {
        let mut msg = GetInteractiveMarkersResponseSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe {
            visualization_msgs__srv__GetInteractiveMarkers_Response__Sequence__fini(&mut msg)
        };
    }
}

unsafe impl<const N: usize> Send for GetInteractiveMarkersResponseSeq<N> {}
unsafe impl<const N: usize> Sync for GetInteractiveMarkersResponseSeq<N> {}

pub struct GetInteractiveMarkers;

impl ServiceMsg for GetInteractiveMarkers {
    type Request = GetInteractiveMarkersRequest;
    type Response = GetInteractiveMarkersResponse;
    fn type_support() -> *const rcl::rosidl_service_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_service_type_support_handle__visualization_msgs__srv__GetInteractiveMarkers()
        }
    }
}
