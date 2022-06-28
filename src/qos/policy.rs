//! Policies of QoS.

use crate::rcl;
use num_derive::{FromPrimitive, ToPrimitive};

/// QoS history enumerations describing how samples endure
#[repr(u32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, FromPrimitive, ToPrimitive)]
pub enum HistoryPolicy {
    /// Implementation default for history policy
    SystemDefault = rcl::rmw_qos_history_policy_t_RMW_QOS_POLICY_HISTORY_SYSTEM_DEFAULT,

    /// Only store up to a maximum number of samples, dropping oldest once max is exceeded
    KeepLast = rcl::rmw_qos_history_policy_t_RMW_QOS_POLICY_HISTORY_KEEP_LAST,

    /// Store all samples, subject to resource limits
    KeepAll = rcl::rmw_qos_history_policy_t_RMW_QOS_POLICY_HISTORY_KEEP_ALL,

    /// History policy has not yet been set
    Unknown = rcl::rmw_qos_history_policy_t_RMW_QOS_POLICY_HISTORY_UNKNOWN,
}

/// QoS Reliability enumerations describing how messages are delivered
#[repr(u32)]
#[derive(Debug, Clone, PartialEq, Eq, FromPrimitive, ToPrimitive)]
pub enum ReliabilityPolicy {
    /// Implementation specific default
    SystemDefault = rcl::rmw_qos_reliability_policy_t_RMW_QOS_POLICY_RELIABILITY_SYSTEM_DEFAULT,

    /// Guarantee that samples are delivered, may retry multiple times.
    Reliable = rcl::rmw_qos_reliability_policy_t_RMW_QOS_POLICY_RELIABILITY_RELIABLE,

    /// Attempt to deliver samples, but some may be lost if the network is not robust
    BestEffort = rcl::rmw_qos_reliability_policy_t_RMW_QOS_POLICY_RELIABILITY_BEST_EFFORT,

    /// Reliability policy has not yet been set
    Unknown = rcl::rmw_qos_reliability_policy_t_RMW_QOS_POLICY_RELIABILITY_UNKNOWN,
}

/// QoS durability enumerations describing how samples persist
#[repr(u32)]
#[derive(Debug, Clone, PartialEq, Eq, FromPrimitive, ToPrimitive)]
pub enum DurabilityPolicy {
    /// Impplementation specific default
    SystemDefault = rcl::rmw_qos_durability_policy_t_RMW_QOS_POLICY_DURABILITY_SYSTEM_DEFAULT,

    /// The rmw publisher is responsible for persisting samples for “late-joining” subscribers
    TransientLocal = rcl::rmw_qos_durability_policy_t_RMW_QOS_POLICY_DURABILITY_TRANSIENT_LOCAL,

    /// Samples are not persistent
    Volatile = rcl::rmw_qos_durability_policy_t_RMW_QOS_POLICY_DURABILITY_VOLATILE,

    /// Durability policy has not yet been set
    Unknown = rcl::rmw_qos_durability_policy_t_RMW_QOS_POLICY_DURABILITY_UNKNOWN,
}

/// QoS liveliness enumerations that describe a publisher's reporting policy for its alive status.
/// For a subscriber, these are its requirements for its topic's publishers.
#[repr(u32)]
#[derive(Debug, Clone, PartialEq, Eq, FromPrimitive, ToPrimitive)]
pub enum LivelinessPolicy {
    /// Implementation specific default
    SystemDefault = rcl::rmw_qos_liveliness_policy_t_RMW_QOS_POLICY_LIVELINESS_SYSTEM_DEFAULT,

    /// The signal that establishes a Topic is alive comes from the ROS rmw layer.
    Automatic = rcl::rmw_qos_liveliness_policy_t_RMW_QOS_POLICY_LIVELINESS_AUTOMATIC,

    /// Explicitly asserting node liveliness is required in this case.
    /// This option is deprecated, use RMW_QOS_POLICY_LIVELINESS_MANUAL_BY_TOPIC if your application
    /// requires to assert liveliness manually.
    #[deprecated]
    ManualByNode = rcl::rmw_qos_liveliness_policy_t_RMW_QOS_POLICY_LIVELINESS_MANUAL_BY_NODE,

    /// The signal that establishes a Topic is alive is at the Topic level. Only publishing a message
    /// on the Topic or an explicit signal from the application to assert liveliness on the Topic
    /// will mark the Topic as being alive.
    ManualByTopic = rcl::rmw_qos_liveliness_policy_t_RMW_QOS_POLICY_LIVELINESS_MANUAL_BY_TOPIC,

    /// Liveliness policy has not yet been set
    Unknown = rcl::rmw_qos_liveliness_policy_t_RMW_QOS_POLICY_LIVELINESS_UNKNOWN,
}
