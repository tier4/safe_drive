use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::FromPrimitive;

use crate::rcl;
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
        write!(f, "{:?} ({})", self, self.clone() as u32)
    }
}

impl Error for RCLError {}

pub type RCLResult<T> = Result<T, RCLError>;
pub type DynError = Box<dyn Error + Send + Sync + 'static>;

/// Convert a rcl-style, C-style, return value to a Rust-style value.
/// If `n` indicates successful, this returns Ok(()),
/// otherwise returns Err(_).
pub fn ret_val_to_err(n: rcl::rcl_ret_t) -> RCLResult<()> {
    let n = n as u32;
    if n == rcl::RCL_RET_OK {
        Ok(())
    } else {
        Err(FromPrimitive::from_u32(n).unwrap_or(RCLError::InvalidRetVal))
    }
}
