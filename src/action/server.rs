use std::{ffi::CString, mem::MaybeUninit, sync::Arc, time::Duration};

use crate::{
    clock::Clock,
    error::{DynError, RCLActionError, RCLActionResult},
    get_allocator,
    msg::{
        builtin_interfaces,
        interfaces::action_msgs::{
            msg::{GoalInfo, GoalInfoSeq},
            srv::{ERROR_NONE, ERROR_REJECTED},
        },
        unique_identifier_msgs::msg::UUID,
        ActionGoal, ActionMsg, GetUUID, GoalResponse,
    },
    node::Node,
    qos::Profile,
    rcl::{
        self, action_msgs__msg__GoalInfo, action_msgs__msg__GoalInfo__Sequence,
        action_msgs__srv__CancelGoal_Request, action_msgs__srv__CancelGoal_Response,
        rcl_action_cancel_request_t, rcutils_get_error_string, unique_identifier_msgs__msg__UUID,
    },
    RecvResult,
};

#[cfg(feature = "galactic")]
use crate::qos::galactic::*;

#[cfg(feature = "humble")]
use crate::qos::humble::*;

use super::SendGoalServiceRequest;

type CancelRequest = action_msgs__srv__CancelGoal_Request;
type CancelResponse = action_msgs__srv__CancelGoal_Response;

pub struct ServerQosOption {
    pub goal_service: Profile,
    pub result_service: Profile,
    pub cancel_service: Profile,
    pub feedback_topic: Profile,
    pub status_topic: Profile,
    pub result_timeout: Duration,
}

impl Default for ServerQosOption {
    fn default() -> Self {
        let status_topic_profile = Profile {
            history: HistoryPolicy::KeepLast,
            depth: 1,
            reliability: ReliabilityPolicy::Reliable,
            durability: DurabilityPolicy::TransientLocal,
            liveliness: LivelinessPolicy::SystemDefault,
            avoid_ros_namespace_conventions: false,
            ..Default::default()
        };

        Self {
            goal_service: Profile::services_default(),
            result_service: Profile::services_default(),
            cancel_service: Profile::services_default(),
            feedback_topic: Profile::default(),
            status_topic: status_topic_profile,
            result_timeout: Duration::from_secs(15 * 60),
        }
    }
}

impl From<ServerQosOption> for rcl::rcl_action_server_options_t {
    fn from(opts: ServerQosOption) -> Self {
        rcl::rcl_action_server_options_t {
            goal_service_qos: (&opts.goal_service).into(),
            cancel_service_qos: (&opts.cancel_service).into(),
            result_service_qos: (&opts.result_service).into(),
            feedback_topic_qos: (&opts.feedback_topic).into(),
            status_topic_qos: (&opts.status_topic).into(),
            allocator: get_allocator(),
            result_timeout: rcl::rcl_duration_t {
                nanoseconds: opts.result_timeout.as_nanos() as i64,
            },
        }
    }
}

/// An action server.
pub struct Server<T: ActionMsg> {
    server: rcl::rcl_action_server_t,
    node: Arc<Node>,
    clock: Clock,

    /// Handler for goal requests from clients.
    goal_request_callback: Box<dyn Fn(SendGoalServiceRequest<T>) -> bool>,
    cancel_request_callback: Box<dyn Fn(CancelRequest) -> bool>,
}

impl<T> Server<T>
where
    T: ActionMsg,
{
    /// Create a server.
    pub fn new<GR, CR>(
        node: Arc<Node>,
        action_name: &str,
        qos: Option<ServerQosOption>,
        goal_request_callback: GR,
        cancel_request_callback: CR,
    ) -> RCLActionResult<Self>
    where
        GR: Fn(SendGoalServiceRequest<T>) -> bool + 'static,
        CR: Fn(CancelRequest) -> bool + 'static,
    {
        let mut server = rcl::MTSafeFn::rcl_action_get_zero_initialized_server();
        let options = qos
            .map(rcl::rcl_action_server_options_t::from)
            .unwrap_or(rcl::MTSafeFn::rcl_action_server_get_default_options());
        // TODO: reconcile RCLResult and RCLActionResult to avoid unwrap
        let clock = Clock::new().unwrap();
        let action_name = CString::new(action_name).unwrap_or_default();

        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_action_server_init(
                &mut server,
                unsafe { node.as_ptr_mut() },
                clock.as_ptr_mut(),
                T::type_support(),
                action_name.as_ptr(),
                &options,
            )?;
        }

        let mut server = Self {
            server,
            node,
            clock,
            goal_request_callback: Box::new(goal_request_callback),
            cancel_request_callback: Box::new(cancel_request_callback),
        };
        server.publish_status().unwrap();

        Ok(server)
    }

    pub fn try_recv_goal_request(&mut self) -> RecvResult<(), ()> {
        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut request: SendGoalServiceRequest<T> = unsafe { MaybeUninit::zeroed().assume_init() };
        let result = {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_action_take_goal_request(
                &self.server,
                &mut header,
                &mut request as *const _ as *mut _,
            )
        };

        match result {
            Ok(()) => {
                // get current time
                let now_nanosec = self.clock.get_now().unwrap();
                let now_sec = now_nanosec / 10_i64.pow(9);
                let stamp = builtin_interfaces::UnsafeTime {
                    sec: now_sec as i32,
                    nanosec: (now_nanosec - now_sec * 10_i64.pow(9)) as u32,
                };

                // accept goal if appropriate
                let callback = &self.goal_request_callback;
                let accepted = callback(request.clone());

                if accepted {
                    // see rcl_interfaces/action_msgs/msg/GoalInfo.msg for definition
                    let mut goal_info = rcl::MTSafeFn::rcl_action_get_zero_initialized_goal_info();

                    let uuid = request.get_uuid().clone();
                    goal_info.goal_id = unique_identifier_msgs__msg__UUID { uuid };

                    goal_info.stamp.sec = (now_nanosec / 10_i64.pow(9)) as i32;
                    goal_info.stamp.nanosec = (now_nanosec - now_sec * 10_i64.pow(9)) as u32;

                    let goal_handle = {
                        let guard = rcl::MT_UNSAFE_FN.lock();
                        guard.rcl_action_accept_new_goal(&mut self.server, &goal_info)
                    };
                    if goal_handle.is_null() {
                        let msg = unsafe { rcutils_get_error_string() };
                        return RecvResult::Err(format!("Failed to accept new goal: {msg}").into());
                    }

                    self.publish_status().unwrap();
                }

                // TODO: Make SendgoalServiceResponse independent of T (edit safe-drive-msg)
                // SendGoal
                type GoalResponse<T> = <<T as ActionMsg>::Goal as ActionGoal>::Response;

                let mut response = GoalResponse::<T>::new(accepted, stamp);
                // let mut response = SendGoalServiceResponse { accepted, stamp };

                // send response to client
                let guard = rcl::MT_UNSAFE_FN.lock();
                match guard.rcl_action_send_goal_response(
                    &self.server,
                    &mut header,
                    &mut response as *const _ as *mut _,
                ) {
                    Ok(()) => RecvResult::Ok(()),
                    Err(e) => RecvResult::Err(e.into()),
                }
            }
            Err(RCLActionError::ServerTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    pub fn try_recv_cancel_request(&mut self) -> RecvResult<(), ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut request: rcl_action_cancel_request_t =
            rcl::MTSafeFn::rcl_action_get_zero_initialized_cancel_request();

        match guard.rcl_action_take_cancel_request(
            &self.server,
            &mut header,
            &mut request as *const _ as *mut _,
        ) {
            Ok(()) => {
                let mut process_response =
                    rcl::MTSafeFn::rcl_action_get_zero_initialized_cancel_response();

                // compute which exact goals are requested to be cancelled
                match guard.rcl_action_process_cancel_request(
                    &self.server,
                    &request,
                    &mut process_response as *const _ as *mut _,
                ) {
                    Ok(()) => {}
                    // TODO: handle ERROR_UNKNOWN_GOAL_ID etc.
                    Err(e) => return RecvResult::Err(e.into()),
                }

                let goal_seq_ptr =
                    &process_response.msg.goals_canceling as *const _ as *const GoalInfoSeq<0>;
                let candidates = unsafe { &(*goal_seq_ptr) };

                let mut accepted_goals = vec![];
                for goal in candidates.iter() {
                    let callback = &self.cancel_request_callback;
                    let accepted = callback(request);

                    if accepted {
                        accepted_goals.push(goal);
                    }
                }

                let mut cancel_response =
                    rcl::MTSafeFn::rcl_action_get_zero_initialized_cancel_response();

                cancel_response.msg.return_code = if accepted_goals.is_empty() {
                    ERROR_REJECTED
                } else {
                    ERROR_NONE
                };
                let seq = action_msgs__msg__GoalInfo__Sequence {
                    data: accepted_goals.as_mut_ptr() as *mut _ as *mut action_msgs__msg__GoalInfo,
                    size: accepted_goals.len(),
                    capacity: accepted_goals.capacity(),
                };
                cancel_response.msg.goals_canceling = seq;
                // cancel_response.msg.return_code = ERROR_NONE;
                // cancel_response.msg.goals_canceling = process_response.msg.goals_canceling;

                match guard.rcl_action_send_cancel_response(
                    &self.server,
                    &mut header,
                    &mut cancel_response.msg as *const _ as *mut _,
                ) {
                    Ok(()) => RecvResult::Ok(()),
                    Err(e) => RecvResult::Err(e.into()),
                }
            }
            Err(RCLActionError::ServerTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    // TODO: when to publish?
    fn publish_status(&mut self) -> Result<(), DynError> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut status = rcl::MTSafeFn::rcl_action_get_zero_initialized_goal_status_array();
        guard.rcl_action_get_goal_status_array(&self.server, &mut status)?;
        guard.rcl_action_publish_status(&self.server, &status as *const _ as *const _)?;

        Ok(())
    }

    // TODO: try_recv_data? (see rclcpp's take_data)
}

impl<T: ActionMsg> Drop for Server<T> {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_action_server_fini(&mut self.server, unsafe { self.node.as_ptr_mut() });
    }
}

impl From<action_msgs__msg__GoalInfo> for GoalInfo {
    fn from(value: action_msgs__msg__GoalInfo) -> Self {
        Self {
            goal_id: value.goal_id.into(),
            stamp: value.stamp.into(),
        }
    }
}

impl From<unique_identifier_msgs__msg__UUID> for UUID {
    fn from(value: unique_identifier_msgs__msg__UUID) -> Self {
        Self { uuid: value.uuid }
    }
}

impl From<crate::rcl::builtin_interfaces__msg__Time> for crate::msg::builtin_interfaces__msg__Time {
    fn from(value: crate::rcl::builtin_interfaces__msg__Time) -> Self {
        Self {
            sec: value.sec,
            nanosec: value.nanosec,
        }
    }
}
