use crate::rcl;
use core::convert::From;
use std::{error::Error, fmt};

#[derive(Debug, Clone)]
pub enum RCLError {
    Error = 1,
    Timeout = 2,
    BadAlloc = 10,
    InvalidArgument = 11,
    Unsupported = 3,
    AlreadyInit = 100,
    NotInit = 101,
    MismatchedRmwId = 102,
    TopicNameInvalid = 103,
    ServiceNameInvalid = 104,
    UnknownSubstitution = 105,
    AlreadyShutdown = 106,
    NodeInvalid = 200,
    NodeInvalidName = 201,
    NodeInvalidNamespace = 202,
    NodeNameNonExistent = 203,
    PublisherInvalid = 300,
    SubscriptionInvalid = 400,
    SubscriptionTakeFailed = 401,
    ClientInvalid = 500,
    ClientTakeFailed = 501,
    ServiceInvalid = 600,
    ServiceTakeFailed = 601,
    TimerInvalid = 800,
    TimerCanceled = 801,
    WaitSetInvalid = 900,
    WaitSetEmpty = 901,
    WaitSetFull = 902,
    InvalidRemapRule = 1001,
    WrongLexeme = 1002,
    InvalidRosArgs = 1003,
    InvalidParamRule = 1010,
    InvalidLogLevelRule = 1020,
    EventInvalid = 2000,
    EventTakeFailed = 2001,
    LifecycleStateRegistered = 3000,
    LifecycleStateNotRegistered = 3001,
    InvalidRetVal = !0,
}

impl From<u32> for RCLError {
    fn from(n: u32) -> Self {
        match n {
            rcl::RCL_RET_ERROR => RCLError::Error,
            rcl::RCL_RET_TIMEOUT => RCLError::Timeout,
            rcl::RCL_RET_BAD_ALLOC => RCLError::BadAlloc,
            rcl::RCL_RET_INVALID_ARGUMENT => RCLError::InvalidArgument,
            rcl::RCL_RET_UNSUPPORTED => RCLError::Unsupported,
            rcl::RCL_RET_ALREADY_INIT => RCLError::AlreadyInit,
            rcl::RCL_RET_NOT_INIT => RCLError::NotInit,
            rcl::RCL_RET_MISMATCHED_RMW_ID => RCLError::MismatchedRmwId,
            rcl::RCL_RET_TOPIC_NAME_INVALID => RCLError::TopicNameInvalid,
            rcl::RCL_RET_SERVICE_NAME_INVALID => RCLError::ServiceNameInvalid,
            rcl::RCL_RET_UNKNOWN_SUBSTITUTION => RCLError::UnknownSubstitution,
            rcl::RCL_RET_ALREADY_SHUTDOWN => RCLError::AlreadyShutdown,
            rcl::RCL_RET_NODE_INVALID => RCLError::NodeInvalid,
            rcl::RCL_RET_NODE_INVALID_NAME => RCLError::NodeInvalidName,
            rcl::RCL_RET_NODE_INVALID_NAMESPACE => RCLError::NodeInvalidNamespace,
            rcl::RCL_RET_NODE_NAME_NON_EXISTENT => RCLError::NodeNameNonExistent,
            rcl::RCL_RET_PUBLISHER_INVALID => RCLError::PublisherInvalid,
            rcl::RCL_RET_SUBSCRIPTION_INVALID => RCLError::SubscriptionInvalid,
            rcl::RCL_RET_SUBSCRIPTION_TAKE_FAILED => RCLError::SubscriptionTakeFailed,
            rcl::RCL_RET_CLIENT_INVALID => RCLError::ClientInvalid,
            rcl::RCL_RET_CLIENT_TAKE_FAILED => RCLError::ClientTakeFailed,
            rcl::RCL_RET_SERVICE_INVALID => RCLError::ServiceInvalid,
            rcl::RCL_RET_SERVICE_TAKE_FAILED => RCLError::ServiceTakeFailed,
            rcl::RCL_RET_TIMER_INVALID => RCLError::TimerInvalid,
            rcl::RCL_RET_TIMER_CANCELED => RCLError::TimerCanceled,
            rcl::RCL_RET_WAIT_SET_INVALID => RCLError::WaitSetInvalid,
            rcl::RCL_RET_WAIT_SET_EMPTY => RCLError::WaitSetEmpty,
            rcl::RCL_RET_WAIT_SET_FULL => RCLError::WaitSetFull,
            rcl::RCL_RET_INVALID_REMAP_RULE => RCLError::InvalidRemapRule,
            rcl::RCL_RET_WRONG_LEXEME => RCLError::WrongLexeme,
            rcl::RCL_RET_INVALID_ROS_ARGS => RCLError::InvalidRosArgs,
            rcl::RCL_RET_INVALID_PARAM_RULE => RCLError::InvalidParamRule,
            rcl::RCL_RET_INVALID_LOG_LEVEL_RULE => RCLError::InvalidLogLevelRule,
            rcl::RCL_RET_EVENT_INVALID => RCLError::EventInvalid,
            rcl::RCL_RET_EVENT_TAKE_FAILED => RCLError::EventTakeFailed,
            rcl::RCL_RET_LIFECYCLE_STATE_REGISTERED => RCLError::LifecycleStateRegistered,
            rcl::RCL_RET_LIFECYCLE_STATE_NOT_REGISTERED => RCLError::LifecycleStateNotRegistered,
            _ => RCLError::InvalidRetVal,
        }
    }
}

impl fmt::Display for RCLError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} ({})", self, self.clone() as u32)
    }
}

impl Error for RCLError {}

pub type RCLResult<T> = Result<T, RCLError>;

/// Convert a rcl-style (c-style) return value to a Rust-style value.
/// If `n` indicates successful, this returns Ok(()),
/// otherwise returns Err(_).
pub fn ret_val_to_err(n: rcl::rcl_ret_t) -> RCLResult<()> {
    let n = n as u32;
    if n == rcl::RCL_RET_OK {
        Ok(())
    } else {
        Err(RCLError::from(n))
    }
}
