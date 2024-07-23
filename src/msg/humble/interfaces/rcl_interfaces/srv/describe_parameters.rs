// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::super::*;
use crate::msg::common_interfaces::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn rcl_interfaces__srv__DescribeParameters_Request__init(
        msg: *mut DescribeParametersRequest,
    ) -> bool;
    fn rcl_interfaces__srv__DescribeParameters_Request__fini(msg: *mut DescribeParametersRequest);
    fn rcl_interfaces__srv__DescribeParameters_Request__Sequence__init(
        msg: *mut DescribeParametersRequestSeqRaw,
        size: usize,
    ) -> bool;
    fn rcl_interfaces__srv__DescribeParameters_Request__Sequence__fini(
        msg: *mut DescribeParametersRequestSeqRaw,
    );
    fn rcl_interfaces__srv__DescribeParameters_Response__init(
        msg: *mut DescribeParametersResponse,
    ) -> bool;
    fn rcl_interfaces__srv__DescribeParameters_Response__fini(msg: *mut DescribeParametersResponse);
    fn rcl_interfaces__srv__DescribeParameters_Response__Sequence__init(
        msg: *mut DescribeParametersResponseSeqRaw,
        size: usize,
    ) -> bool;
    fn rcl_interfaces__srv__DescribeParameters_Response__Sequence__fini(
        msg: *mut DescribeParametersResponseSeqRaw,
    );
    fn rosidl_typesupport_c__get_service_type_support_handle__rcl_interfaces__srv__DescribeParameters(
    ) -> *const rcl::rosidl_service_type_support_t;
    fn rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__DescribeParameters_Request(
    ) -> *const rcl::rosidl_message_type_support_t;
    fn rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__DescribeParameters_Response(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct DescribeParametersRequest {
    pub names: crate::msg::RosStringSeq<0, 0>,
}

#[repr(C)]
#[derive(Debug)]
pub struct DescribeParametersResponse {
    pub descriptors: ParameterDescriptorSeq<0>,
}

impl DescribeParametersRequest {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__DescribeParameters_Request__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for DescribeParametersRequest {
    fn drop(&mut self) {
        unsafe { rcl_interfaces__srv__DescribeParameters_Request__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct DescribeParametersRequestSeqRaw {
    data: *mut DescribeParametersRequest,
    size: size_t,
    capacity: size_t,
}

/// Sequence of DescribeParametersRequest.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct DescribeParametersRequestSeq<const N: usize> {
    data: *mut DescribeParametersRequest,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> DescribeParametersRequestSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: DescribeParametersRequestSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe {
            rcl_interfaces__srv__DescribeParameters_Request__Sequence__init(&mut msg, size)
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

    pub fn null() -> Self {
        let msg: DescribeParametersRequestSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[DescribeParametersRequest] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [DescribeParametersRequest] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, DescribeParametersRequest> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, DescribeParametersRequest> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for DescribeParametersRequestSeq<N> {
    fn drop(&mut self) {
        let mut msg = DescribeParametersRequestSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { rcl_interfaces__srv__DescribeParameters_Request__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for DescribeParametersRequestSeq<N> {}
unsafe impl<const N: usize> Sync for DescribeParametersRequestSeq<N> {}

impl DescribeParametersResponse {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__DescribeParameters_Response__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for DescribeParametersResponse {
    fn drop(&mut self) {
        unsafe { rcl_interfaces__srv__DescribeParameters_Response__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct DescribeParametersResponseSeqRaw {
    data: *mut DescribeParametersResponse,
    size: size_t,
    capacity: size_t,
}

/// Sequence of DescribeParametersResponse.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct DescribeParametersResponseSeq<const N: usize> {
    data: *mut DescribeParametersResponse,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> DescribeParametersResponseSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: DescribeParametersResponseSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe {
            rcl_interfaces__srv__DescribeParameters_Response__Sequence__init(&mut msg, size)
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

    pub fn null() -> Self {
        let msg: DescribeParametersResponseSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[DescribeParametersResponse] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [DescribeParametersResponse] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, DescribeParametersResponse> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, DescribeParametersResponse> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for DescribeParametersResponseSeq<N> {
    fn drop(&mut self) {
        let mut msg = DescribeParametersResponseSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { rcl_interfaces__srv__DescribeParameters_Response__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for DescribeParametersResponseSeq<N> {}
unsafe impl<const N: usize> Sync for DescribeParametersResponseSeq<N> {}

pub struct DescribeParameters;

impl ServiceMsg for DescribeParameters {
    type Request = DescribeParametersRequest;
    type Response = DescribeParametersResponse;
    fn type_support() -> *const rcl::rosidl_service_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_service_type_support_handle__rcl_interfaces__srv__DescribeParameters()
        }
    }
}

impl TypeSupport for DescribeParametersRequest {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__DescribeParameters_Request()
        }
    }
}

impl TypeSupport for DescribeParametersResponse {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__DescribeParameters_Response()
        }
    }
}
