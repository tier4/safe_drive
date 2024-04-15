//! QoS of ROS2.

#[cfg(feature = "galactic")]
pub mod galactic;

#[cfg(feature = "humble")]
pub mod humble;

#[cfg(feature = "iron")]
pub mod iron;

pub mod policy;

// pub mod policy;

use crate::rcl;
use num_traits::{FromPrimitive, ToPrimitive};
use policy::*;
use std::time::Duration;

/// Represent QoS profile.
#[derive(Debug, Clone)]
pub struct Profile {
    /// Keep last: only store up to N samples, configurable via the queue depth option.
    /// Keep all: store all samples, subject to the configured resource limits of the underlying middleware.
    pub history: HistoryPolicy,

    /// Size of the message queue.
    pub depth: usize,

    /// Reliabiilty QoS policy setting.
    pub reliability: ReliabilityPolicy,

    /// Durability QoS policy setting.
    pub durability: DurabilityPolicy,

    /// The period at which messages are expected to be sent/received.
    /// RMW_DURATION_UNSPEFICIED will use the RMW implementation's default value,
    /// which may or may not be infinite.
    /// RMW_DURATION_INFINITE explicitly states that messages never miss a deadline expectation.
    pub deadline: Duration,

    /// The age at which messages are considered expired and no longer valid.
    /// RMW_DURATION_UNSPEFICIED will use the RMW implementation's default value,
    /// which may or may not be infinite.
    /// RMW_DURATION_INFINITE explicitly states that messages do not expire.
    pub lifespan: Duration,

    /// Liveliness QoS policy setting.
    pub liveliness: LivelinessPolicy,

    /// The time within which the RMW node or publisher must show that it is alive.
    /// RMW_DURATION_UNSPEFICIED will use the RMW implementation's default value,
    /// which may or may not be infinite.
    /// RMW_DURATION_INFINITE explicitly states that liveliness is not enforced.
    pub liveliness_lease_duration: Duration,

    /// If true, any ROS specific namespacing conventions will be circumvented.
    /// In the case of DDS and topics, for example, this means the typical
    /// ROS specific prefix of `rt` would not be applied as described here:
    /// <http://design.ros2.org/articles/topic_and_service_names.html#ros-specific-namespace-prefix>.
    /// This might be useful when trying to directly connect a native DDS topic
    /// with a ROS 2 topic.
    pub avoid_ros_namespace_conventions: bool,
}

impl Default for Profile {
    /// Default QoS class
    /// - History: Keep last,
    /// - Depth: 10,
    /// - Reliability: Reliable,
    /// - Durability: Volatile,
    /// - Deadline: Default,
    /// - Lifespan: Default,
    /// - Liveliness: System default,
    /// - Liveliness lease duration: Default,
    /// - Avoid ros namespace conventions: false
    fn default() -> Self {
        Self {
            history: HistoryPolicy::KeepLast,
            depth: 10,
            reliability: ReliabilityPolicy::Reliable,
            durability: DurabilityPolicy::Volatile,
            ..Self::common()
        }
    }
}

impl Profile {
    const fn common() -> Self {
        Self {
            history: HistoryPolicy::SystemDefault,
            depth: rcl::RMW_QOS_POLICY_DEPTH_SYSTEM_DEFAULT as usize,
            reliability: ReliabilityPolicy::SystemDefault,
            durability: DurabilityPolicy::SystemDefault,
            deadline: Duration::ZERO,
            lifespan: Duration::ZERO,
            liveliness: LivelinessPolicy::SystemDefault,
            liveliness_lease_duration: Duration::ZERO,
            avoid_ros_namespace_conventions: false,
        }
    }

    /// Services QoS class
    /// - History: Keep last,
    /// - Depth: 10,
    /// - Reliability: Reliable,
    /// - Durability: Volatile,
    /// - Deadline: Default,
    /// - Lifespan: Default,
    /// - Liveliness: System default,
    /// - Liveliness lease duration: Default,
    /// - Avoid ros namespace conventions: false
    pub fn services_default() -> Self {
        Self {
            history: HistoryPolicy::KeepLast,
            depth: 10,
            reliability: ReliabilityPolicy::Reliable,
            durability: DurabilityPolicy::Volatile,
            ..Self::common()
        }
    }

    /// Sensor Data QoS class
    /// - History: Keep last,
    /// - Depth: 5,
    /// - Reliability: Best effort,
    /// - Durability: Volatile,
    /// - Deadline: Default,
    /// - Lifespan: Default,
    /// - Liveliness: System default,
    /// - Liveliness lease duration: Default,
    /// - avoid ros namespace conventions: false
    pub const fn sensor_data() -> Self {
        Self {
            history: HistoryPolicy::KeepLast,
            depth: 5,
            reliability: ReliabilityPolicy::BestEffort,
            durability: DurabilityPolicy::Volatile,
            ..Self::common()
        }
    }

    /// Parameters QoS class
    /// - History: Keep last,
    /// - Depth: 1000,
    /// - Reliability: Reliable,
    /// - Durability: Volatile,
    /// - Deadline: Default,
    /// - Lifespan: Default,
    /// - Liveliness: System default,
    /// - Liveliness lease duration: Default,
    /// - Avoid ros namespace conventions: false
    pub const fn parameters() -> Self {
        Self {
            history: HistoryPolicy::KeepLast,
            depth: 1000,
            reliability: ReliabilityPolicy::Reliable,
            durability: DurabilityPolicy::Volatile,
            ..Self::common()
        }
    }
}

impl From<&rcl::rmw_qos_profile_t> for Profile {
    fn from(qos: &rcl::rmw_qos_profile_t) -> Self {
        Self {
            history: FromPrimitive::from_u32(qos.history).unwrap_or(HistoryPolicy::Unknown),
            depth: qos.depth.try_into().unwrap(),
            reliability: FromPrimitive::from_u32(qos.reliability)
                .unwrap_or(ReliabilityPolicy::Unknown),
            durability: FromPrimitive::from_u32(qos.durability)
                .unwrap_or(DurabilityPolicy::Unknown),
            liveliness: FromPrimitive::from_u32(qos.liveliness)
                .unwrap_or(LivelinessPolicy::Unknown),
            deadline: qos.deadline.into(),
            lifespan: qos.lifespan.into(),
            liveliness_lease_duration: qos.liveliness_lease_duration.into(),
            avoid_ros_namespace_conventions: qos.avoid_ros_namespace_conventions,
        }
    }
}

impl From<&Profile> for rcl::rmw_qos_profile_t {
    #[cfg(feature = "galactic")]
    fn from(qos: &Profile) -> Self {
        rcl::rmw_qos_profile_t {
            history: ToPrimitive::to_u32(&qos.history)
                .unwrap_or(rcl::rmw_qos_history_policy_t_RMW_QOS_POLICY_HISTORY_UNKNOWN),
            depth: qos.depth as u64,
            reliability: ToPrimitive::to_u32(&qos.reliability)
                .unwrap_or(rcl::rmw_qos_reliability_policy_t_RMW_QOS_POLICY_RELIABILITY_UNKNOWN),
            durability: ToPrimitive::to_u32(&qos.durability)
                .unwrap_or(rcl::rmw_qos_durability_policy_t_RMW_QOS_POLICY_DURABILITY_UNKNOWN),
            liveliness: ToPrimitive::to_u32(&qos.liveliness)
                .unwrap_or(rcl::rmw_qos_liveliness_policy_t_RMW_QOS_POLICY_LIVELINESS_UNKNOWN),
            deadline: qos.deadline.into(),
            lifespan: qos.lifespan.into(),
            liveliness_lease_duration: qos.liveliness_lease_duration.into(),
            avoid_ros_namespace_conventions: qos.avoid_ros_namespace_conventions,
        }
    }

    #[cfg(any(feature = "humble", feature = "iron"))]
    fn from(qos: &Profile) -> Self {
        rcl::rmw_qos_profile_t {
            history: ToPrimitive::to_u32(&qos.history)
                .unwrap_or(rcl::rmw_qos_history_policy_e_RMW_QOS_POLICY_HISTORY_UNKNOWN),
            depth: qos.depth as _,
            reliability: ToPrimitive::to_u32(&qos.reliability)
                .unwrap_or(rcl::rmw_qos_reliability_policy_e_RMW_QOS_POLICY_RELIABILITY_UNKNOWN),
            durability: ToPrimitive::to_u32(&qos.durability)
                .unwrap_or(rcl::rmw_qos_durability_policy_e_RMW_QOS_POLICY_DURABILITY_UNKNOWN),
            liveliness: ToPrimitive::to_u32(&qos.liveliness)
                .unwrap_or(rcl::rmw_qos_liveliness_policy_e_RMW_QOS_POLICY_LIVELINESS_UNKNOWN),
            deadline: qos.deadline.into(),
            lifespan: qos.lifespan.into(),
            liveliness_lease_duration: qos.liveliness_lease_duration.into(),
            avoid_ros_namespace_conventions: qos.avoid_ros_namespace_conventions,
        }
    }
}
