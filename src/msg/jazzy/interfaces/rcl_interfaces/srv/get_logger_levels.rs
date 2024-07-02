// This file was automatically generated by ros2msg_to_rs (https://github.com/tier4/ros2msg_to_rs).
use super::super::*;
use super::super::super::*;
use crate::msg::*;
use crate::rcl;
use crate::msg::common_interfaces::*;

extern "C" {
    fn rcl_interfaces__srv__GetLoggerLevels_Request__init(msg: *mut GetLoggerLevelsRequest) -> bool;
    fn rcl_interfaces__srv__GetLoggerLevels_Request__fini(msg: *mut GetLoggerLevelsRequest);
    fn rcl_interfaces__srv__GetLoggerLevels_Request__Sequence__init(msg: *mut GetLoggerLevelsRequestSeqRaw, size: usize) -> bool;
    fn rcl_interfaces__srv__GetLoggerLevels_Request__Sequence__fini(msg: *mut GetLoggerLevelsRequestSeqRaw);
    fn rcl_interfaces__srv__GetLoggerLevels_Response__init(msg: *mut GetLoggerLevelsResponse) -> bool;
    fn rcl_interfaces__srv__GetLoggerLevels_Response__fini(msg: *mut GetLoggerLevelsResponse);
    fn rcl_interfaces__srv__GetLoggerLevels_Response__Sequence__init(msg: *mut GetLoggerLevelsResponseSeqRaw, size: usize) -> bool;
    fn rcl_interfaces__srv__GetLoggerLevels_Response__Sequence__fini(msg: *mut GetLoggerLevelsResponseSeqRaw);
    fn rosidl_typesupport_c__get_service_type_support_handle__rcl_interfaces__srv__GetLoggerLevels() -> *const rcl::rosidl_service_type_support_t;
    fn rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__GetLoggerLevels_Request() -> *const rcl::rosidl_message_type_support_t;
    fn rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__GetLoggerLevels_Response() -> *const rcl::rosidl_message_type_support_t;
}


#[repr(C)]
#[derive(Debug)]
pub struct GetLoggerLevelsRequest {
    pub names: crate::msg::RosStringSeq<0, 0>,
}

#[repr(C)]
#[derive(Debug)]
pub struct GetLoggerLevelsResponse {
    pub levels: LoggerLevelSeq<0>,
}

impl GetLoggerLevelsRequest {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__GetLoggerLevels_Request__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for GetLoggerLevelsRequest {
    fn drop(&mut self) {
        unsafe { rcl_interfaces__srv__GetLoggerLevels_Request__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct GetLoggerLevelsRequestSeqRaw {
    data: *mut GetLoggerLevelsRequest,
    size: size_t,
    capacity: size_t,
}

/// Sequence of GetLoggerLevelsRequest.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct GetLoggerLevelsRequestSeq<const N: usize> {
    data: *mut GetLoggerLevelsRequest,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> GetLoggerLevelsRequestSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: GetLoggerLevelsRequestSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__GetLoggerLevels_Request__Sequence__init(&mut msg, size) } {
            Some(Self {data: msg.data, size: msg.size, capacity: msg.capacity })
        } else {
            None
        }
    }

    pub fn null() -> Self {
        let msg: GetLoggerLevelsRequestSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {data: msg.data, size: msg.size, capacity: msg.capacity }
    }

    pub fn as_slice(&self) -> &[GetLoggerLevelsRequest] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [GetLoggerLevelsRequest] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, GetLoggerLevelsRequest> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, GetLoggerLevelsRequest> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for GetLoggerLevelsRequestSeq<N> {
    fn drop(&mut self) {
        let mut msg = GetLoggerLevelsRequestSeqRaw{data: self.data, size: self.size, capacity: self.capacity};
        unsafe { rcl_interfaces__srv__GetLoggerLevels_Request__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for GetLoggerLevelsRequestSeq<N> {}
unsafe impl<const N: usize> Sync for GetLoggerLevelsRequestSeq<N> {}


impl GetLoggerLevelsResponse {
    pub fn new() -> Option<Self> {
        let mut msg: Self = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__GetLoggerLevels_Response__init(&mut msg) } {
            Some(msg)
        } else {
            None
        }
    }
}

impl Drop for GetLoggerLevelsResponse {
    fn drop(&mut self) {
        unsafe { rcl_interfaces__srv__GetLoggerLevels_Response__fini(self) };
    }
}

#[repr(C)]
#[derive(Debug)]
struct GetLoggerLevelsResponseSeqRaw {
    data: *mut GetLoggerLevelsResponse,
    size: size_t,
    capacity: size_t,
}

/// Sequence of GetLoggerLevelsResponse.
/// `N` is the maximum number of elements.
/// If `N` is `0`, the size is unlimited.
#[repr(C)]
#[derive(Debug)]
pub struct GetLoggerLevelsResponseSeq<const N: usize> {
    data: *mut GetLoggerLevelsResponse,
    size: size_t,
    capacity: size_t,
}

impl<const N: usize> GetLoggerLevelsResponseSeq<N> {
    /// Create a sequence of.
    /// `N` represents the maximum number of elements.
    /// If `N` is `0`, the sequence is unlimited.
    pub fn new(size: usize) -> Option<Self> {
        if N != 0 && size > N {
            // the size exceeds in the maximum number
            return None;
        }

        let mut msg: GetLoggerLevelsResponseSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        if unsafe { rcl_interfaces__srv__GetLoggerLevels_Response__Sequence__init(&mut msg, size) } {
            Some(Self {data: msg.data, size: msg.size, capacity: msg.capacity })
        } else {
            None
        }
    }

    pub fn null() -> Self {
        let msg: GetLoggerLevelsResponseSeqRaw = unsafe { std::mem::MaybeUninit::zeroed().assume_init() };
        Self {data: msg.data, size: msg.size, capacity: msg.capacity }
    }

    pub fn as_slice(&self) -> &[GetLoggerLevelsResponse] {
        if self.data.is_null() {
            &[]
        } else {
            let s = unsafe { std::slice::from_raw_parts(self.data, self.size as _) };
            s
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [GetLoggerLevelsResponse] {
        if self.data.is_null() {
            &mut []
        } else {
            let s = unsafe { std::slice::from_raw_parts_mut(self.data, self.size as _) };
            s
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, GetLoggerLevelsResponse> {
        self.as_slice().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, GetLoggerLevelsResponse> {
        self.as_slice_mut().iter_mut()
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> Drop for GetLoggerLevelsResponseSeq<N> {
    fn drop(&mut self) {
        let mut msg = GetLoggerLevelsResponseSeqRaw{data: self.data, size: self.size, capacity: self.capacity};
        unsafe { rcl_interfaces__srv__GetLoggerLevels_Response__Sequence__fini(&mut msg) };
    }
}

unsafe impl<const N: usize> Send for GetLoggerLevelsResponseSeq<N> {}
unsafe impl<const N: usize> Sync for GetLoggerLevelsResponseSeq<N> {}


pub struct GetLoggerLevels;

impl ServiceMsg for GetLoggerLevels {
    type Request = GetLoggerLevelsRequest;
    type Response = GetLoggerLevelsResponse;
    fn type_support() -> *const rcl::rosidl_service_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_service_type_support_handle__rcl_interfaces__srv__GetLoggerLevels()
        }
    }
}

impl TypeSupport for GetLoggerLevelsRequest {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__GetLoggerLevels_Request()
        }
    }
}

impl TypeSupport for GetLoggerLevelsResponse {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            rosidl_typesupport_c__get_message_type_support_handle__rcl_interfaces__srv__GetLoggerLevels_Response()
        }
    }
}

