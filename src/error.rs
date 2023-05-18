//! Errors returned by ROS2.

use crate::rcl;
use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::FromPrimitive;
use std::{
    error::Error,
    fmt::{self, Debug},
};

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPrimitive, ToPrimitive)]
pub enum RCLError {
    Error = rcl::RCL_RET_ERROR,
    Timeout = rcl::RCL_RET_TIMEOUT,
    BadAlloc = rcl::RCL_RET_BAD_ALLOC,
    InvalidArgument = rcl::RCL_RET_INVALID_ARGUMENT,
    Unsupported = rcl::RCL_RET_UNSUPPORTED,
    AlreadyInit = rcl::RCL_RET_ALREADY_INIT,
    NotInit = rcl::RCL_RET_NOT_INIT,
    MismatchedRmwId = rcl::RCL_RET_MISMATCHED_RMW_ID,
    TopicNameInvalid = rcl::RCL_RET_TOPIC_NAME_INVALID,
    ServiceNameInvalid = rcl::RCL_RET_SERVICE_NAME_INVALID,
    UnknownSubstitution = rcl::RCL_RET_UNKNOWN_SUBSTITUTION,
    AlreadyShutdown = rcl::RCL_RET_ALREADY_SHUTDOWN,
    NodeInvalid = rcl::RCL_RET_NODE_INVALID,
    NodeInvalidName = rcl::RCL_RET_NODE_INVALID_NAME,
    NodeInvalidNamespace = rcl::RCL_RET_NODE_INVALID_NAMESPACE,
    NodeNameNonExistent = rcl::RCL_RET_NODE_NAME_NON_EXISTENT,
    PublisherInvalid = rcl::RCL_RET_PUBLISHER_INVALID,
    SubscriptionInvalid = rcl::RCL_RET_SUBSCRIPTION_INVALID,
    SubscriptionTakeFailed = rcl::RCL_RET_SUBSCRIPTION_TAKE_FAILED,
    ClientInvalid = rcl::RCL_RET_CLIENT_INVALID,
    ClientTakeFailed = rcl::RCL_RET_CLIENT_TAKE_FAILED,
    ServiceInvalid = rcl::RCL_RET_SERVICE_INVALID,
    ServiceTakeFailed = rcl::RCL_RET_SERVICE_TAKE_FAILED,
    TimerInvalid = rcl::RCL_RET_TIMER_INVALID,
    TimerCanceled = rcl::RCL_RET_TIMER_CANCELED,
    WaitSetInvalid = rcl::RCL_RET_WAIT_SET_INVALID,
    WaitSetEmpty = rcl::RCL_RET_WAIT_SET_EMPTY,
    WaitSetFull = rcl::RCL_RET_WAIT_SET_FULL,
    InvalidRemapRule = rcl::RCL_RET_INVALID_REMAP_RULE,
    WrongLexeme = rcl::RCL_RET_WRONG_LEXEME,
    InvalidRosArgs = rcl::RCL_RET_INVALID_ROS_ARGS,
    InvalidParamRule = rcl::RCL_RET_INVALID_PARAM_RULE,
    InvalidLogLevelRule = rcl::RCL_RET_INVALID_LOG_LEVEL_RULE,
    EventInvalid = rcl::RCL_RET_EVENT_INVALID,
    EventTakeFailed = rcl::RCL_RET_EVENT_TAKE_FAILED,
    LifecycleStateRegistered = rcl::RCL_RET_LIFECYCLE_STATE_REGISTERED,
    LifecycleStateNotRegistered = rcl::RCL_RET_LIFECYCLE_STATE_NOT_REGISTERED,
    InvalidRetVal = !0,
}

impl fmt::Display for RCLError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} ({})", self, *self as u32)
    }
}

impl Error for RCLError {}

/// Result type to RCLError when encountering error.
pub type RCLResult<T> = Result<T, RCLError>;

/// Dynamic type which can be sent and shared between threads.
pub type DynError = Box<dyn Error + Send + Sync + 'static>;

/// Convert a rcl-style, C-style, return value to a Rust-style value.
/// If `n` indicates successful, this returns Ok(()),
/// otherwise returns Err(_).
pub(crate) fn ret_val_to_err(n: rcl::rcl_ret_t) -> RCLResult<()> {
    let n = n as u32;
    if n == rcl::RCL_RET_OK {
        Ok(())
    } else {
        Err(FromPrimitive::from_u32(n).unwrap_or(RCLError::InvalidRetVal))
    }
}

//
// Some errors in rcl and rcl_action have the same error code (e.g. RCL_RET_ACTION_NAME_INVALID ==
// RCL_RET_EVENT_INVALID == 2000) so errors in actions are referenced through RCLActionError.
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RCLActionError {
    NameInvalid,
    // RCL_RET_ACTION_GOAL_ACCEPTED and RCL_RET_ACTION_GOAL_REJECTED are not used in RCL
    // and do not represent errors, but are kept here for consistency.
    GoalAccepted,
    GoalRejected,
    ClientInvalid,
    ClientTakeFailed,
    ServerInvalid,
    ServerTakeFailed,
    GoalHandleInvalid,
    GoalEventInvalid,
    RCLError(RCLError),
    InvalidRetVal,
}

impl fmt::Display for RCLActionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} ({})", self, Into::<u32>::into(*self))
    }
}

impl Error for RCLActionError {}

/// Result type to RCLActionError when encountering error.
pub type RCLActionResult<T> = Result<T, RCLActionError>;

pub(crate) fn action_ret_val_to_err(n: rcl::rcl_ret_t) -> RCLActionResult<()> {
    match n as u32 {
        rcl::RCL_RET_OK => Ok(()),
        rcl::RCL_RET_ACTION_NAME_INVALID => Err(RCLActionError::NameInvalid),
        rcl::RCL_RET_ACTION_GOAL_ACCEPTED => Err(RCLActionError::GoalAccepted),
        rcl::RCL_RET_ACTION_GOAL_REJECTED => Err(RCLActionError::GoalRejected),
        rcl::RCL_RET_ACTION_CLIENT_INVALID => Err(RCLActionError::ClientInvalid),
        rcl::RCL_RET_ACTION_CLIENT_TAKE_FAILED => Err(RCLActionError::ClientTakeFailed),
        rcl::RCL_RET_ACTION_SERVER_INVALID => Err(RCLActionError::ServerInvalid),
        rcl::RCL_RET_ACTION_SERVER_TAKE_FAILED => Err(RCLActionError::ServerTakeFailed),
        rcl::RCL_RET_ACTION_GOAL_HANDLE_INVALID => Err(RCLActionError::GoalHandleInvalid),
        rcl::RCL_RET_ACTION_GOAL_EVENT_INVALID => Err(RCLActionError::GoalEventInvalid),

        _ => ret_val_to_err(n).map_err(RCLActionError::RCLError),
    }
}

impl From<RCLActionError> for u32 {
    fn from(val: RCLActionError) -> Self {
        match val {
            RCLActionError::NameInvalid => rcl::RCL_RET_ACTION_NAME_INVALID,
            RCLActionError::GoalAccepted => rcl::RCL_RET_ACTION_GOAL_ACCEPTED,
            RCLActionError::GoalRejected => rcl::RCL_RET_ACTION_GOAL_REJECTED,
            RCLActionError::ClientInvalid => rcl::RCL_RET_ACTION_CLIENT_INVALID,
            RCLActionError::ClientTakeFailed => rcl::RCL_RET_ACTION_CLIENT_TAKE_FAILED,
            RCLActionError::ServerInvalid => rcl::RCL_RET_ACTION_SERVER_INVALID,
            RCLActionError::ServerTakeFailed => rcl::RCL_RET_ACTION_SERVER_TAKE_FAILED,
            RCLActionError::GoalHandleInvalid => rcl::RCL_RET_ACTION_GOAL_HANDLE_INVALID,
            RCLActionError::GoalEventInvalid => rcl::RCL_RET_ACTION_GOAL_EVENT_INVALID,
            RCLActionError::RCLError(err) => err as u32,
            RCLActionError::InvalidRetVal => !0,
        }
    }
}

impl std::fmt::Display for rcl::rcutils_error_string_t {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.str_;
        let inner: &[u8] = unsafe { &*(&s as *const [i8] as *const [u8]) };
        let s = String::from_utf8(inner.to_vec()).unwrap();
        write!(f, "{}", s)
    }
}
