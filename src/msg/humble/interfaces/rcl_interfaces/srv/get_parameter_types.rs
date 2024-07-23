// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::super::*;
use super::super::*;
use crate::msg::common_interfaces::*;
use crate::msg::*;
use crate::rcl;

extern "C" {
    fn rcl_interfaces__srv__GetParameterTypes_Request__init(
        msg: *mut GetParameterTypesRequest,
    ) -> bool;
    fn rcl_interfaces__srv__GetParameterTypes_Request__fini(msg: *mut GetParameterTypesRequest);
    fn rcl_interfaces__srv__GetParameterTypes_Request__Sequence__init(
        msg: *mut GetParameterTypesRequestSeqRaw,
        size: usize,
    ) -> bool;
    fn rcl_interfaces__srv__GetParameterTypes_Request__Sequence__fini(
        msg: *mut GetParameterTypesRequestSeqRaw,
    );
    fn rcl_interfaces__srv__GetParameterTypes_Response__init(
        msg: *mut GetParameterTypesResponse,
    ) -> bool;
    fn rcl_interfaces__srv__GetParameterTypes_Response__fini(msg: *mut GetParameterTypesResponse);
    fn rcl_interfaces__srv__GetParameterTypes_Response__Sequence__init(
        msg: *mut GetParameterTypesResponseSeqRaw,
        size: usize,
    ) -> bool;
    fn rcl_interfaces__srv__GetParameterTypes_Response__Sequence__fini(
        msg: *mut GetParameterTypesResponseSeqRaw,
    );
    fn rosidl_typesupport_c__get_service_type_support_handle__rcl_interfaces__srv__GetParameterTypes(
    ) -> *const rcl::rosidl_service_type_support_t;
    fn rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__GetParameterTypes_Request(
    ) -> *const rcl::rosidl_message_type_support_t;
    fn rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__GetParameterTypes_Response(
    ) -> *const rcl::rosidl_message_type_support_t;
}

#[repr(C)]
#[derive(Debug)]
pub struct GetParameterTypesRequest {
    pub names: crate::msg::RosStringSeq<0, 0>,
}

#[repr(C)]
#[derive(Debug)]
pub struct GetParameterTypesResponse {
    pub types: crate::msg::U8Seq<0>,
}

impl GetParameterTypesRequest {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__GetParameterTypes_Request__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for GetParameterTypesRequest {
    fn drop(&mut self) {
        unsafe { rcl_interfaces__srv__GetParameterTypes_Request__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct GetParameterTypesRequestSeqRaw {
    data: *mut GetParameterTypesRequest,
    size: size_t,
    capacity: size_t,
}

/// Sequence of GetParameterTypesRequest.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct GetParameterTypesRequestSeq<const N: usize> {
    data: *mut GetParameterTypesRequest,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> GetParameterTypesRequestSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: GetParameterTypesRequestSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__GetParameterTypes_Request__Sequence__init(&mut msg, size) }
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

    pub fn null() -> Self {
        let msg: GetParameterTypesRequestSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[GetParameterTypesRequest] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [GetParameterTypesRequest] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, GetParameterTypesRequest> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, GetParameterTypesRequest> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for GetParameterTypesRequestSeq<N> {
    fn drop(&mut self) {
        let mut msg = GetParameterTypesRequestSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { rcl_interfaces__srv__GetParameterTypes_Request__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for GetParameterTypesRequestSeq<N> {}
unsafe impl<const N: usize> Sync for GetParameterTypesRequestSeq<N> {}

impl GetParameterTypesResponse {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__GetParameterTypes_Response__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for GetParameterTypesResponse {
    fn drop(&mut self) {
        unsafe { rcl_interfaces__srv__GetParameterTypes_Response__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct GetParameterTypesResponseSeqRaw {
    data: *mut GetParameterTypesResponse,
    size: size_t,
    capacity: size_t,
}

/// Sequence of GetParameterTypesResponse.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct GetParameterTypesResponseSeq<const N: usize> {
    data: *mut GetParameterTypesResponse,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> GetParameterTypesResponseSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: GetParameterTypesResponseSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe {
            rcl_interfaces__srv__GetParameterTypes_Response__Sequence__init(&mut msg, size)
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
        let msg: GetParameterTypesResponseSeqRaw =
            unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {
            data: msg.data,
            size: msg.size,
            capacity: msg.capacity,
        }
    }

    pub fn as_slice(&self) -> &[GetParameterTypesResponse] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [GetParameterTypesResponse] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, GetParameterTypesResponse> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, GetParameterTypesResponse> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for GetParameterTypesResponseSeq<N> {
    fn drop(&mut self) {
        let mut msg = GetParameterTypesResponseSeqRaw {
            data: self.data,
            size: self.size,
            capacity: self.capacity,
        };
        unsafe { rcl_interfaces__srv__GetParameterTypes_Response__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for GetParameterTypesResponseSeq<N> {}
unsafe impl<const N: usize> Sync for GetParameterTypesResponseSeq<N> {}

pub struct GetParameterTypes;

impl ServiceMsg for GetParameterTypes {
    type Request = GetParameterTypesRequest;
    type Response = GetParameterTypesResponse;
    fn type_support() -> *const rcl::rosidl_service_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_service_type_support_handle__rcl_interfaces__srv__GetParameterTypes()
        }
    }
}

impl TypeSupport for GetParameterTypesRequest {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__GetParameterTypes_Request()
        }
    }
}

impl TypeSupport for GetParameterTypesResponse {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__GetParameterTypes_Response()
        }
    }
}
