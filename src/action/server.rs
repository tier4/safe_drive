use parking_lot::Mutex;
use std::{collections::BTreeMap, ffi::CString, mem::MaybeUninit, sync::Arc, time::Duration};

use crate::{
    clock::Clock,
    error::{DynError, RCLActionError, RCLActionResult},
    get_allocator,
    msg::{
        builtin_interfaces::UnsafeTime, interfaces::action_msgs::msg::GoalInfo,
        unique_identifier_msgs::msg::UUID, ActionGoal, ActionMsg, GoalResponse,
    },
    node::Node,
    qos::Profile,
    rcl::{
        self, action_msgs__msg__GoalInfo, rcl_action_cancel_request_t, rcl_action_goal_handle_t,
        rcl_action_server_t, rmw_request_id_t, unique_identifier_msgs__msg__UUID,
    },
    RecvResult,
};

#[cfg(feature = "galactic")]
use crate::qos::galactic::*;

#[cfg(feature = "humble")]
use crate::qos::humble::*;

use super::{
    handle::GoalHandle, update_goal_status, GetResultServiceRequest, GoalStatus,
    SendGoalServiceRequest,
};

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

pub(crate) struct ActionServerData<T: ActionMsg> {
    server: rcl::rcl_action_server_t,
    pub node: Arc<Node>,

    /// Once the server has completed the result for a goal, it is kept here and the result requests are responsed with the result value in this map.
    pub results: Mutex<BTreeMap<[u8; 16], T::ResultContent>>,
}

impl<T: ActionMsg> ActionServerData<T> {
    pub(crate) unsafe fn as_ptr_mut(&self) -> *mut rcl::rcl_action_server_t {
        &self.server as *const _ as *mut _
    }
}

unsafe impl<T: ActionMsg> Sync for ActionServerData<T> {}
unsafe impl<T: ActionMsg> Send for ActionServerData<T> {}

/// An action server.
pub struct Server<T: ActionMsg> {
    pub(crate) data: Arc<ActionServerData<T>>,
    clock: Clock,
}

impl<T> Server<T>
where
    T: ActionMsg,
{
    /// Create a server.
    pub fn new(
        node: Arc<Node>,
        action_name: &str,
        qos: Option<ServerQosOption>,
    ) -> RCLActionResult<Self> {
        let mut server = rcl::MTSafeFn::rcl_action_get_zero_initialized_server();
        let options = qos
            .map(rcl::rcl_action_server_options_t::from)
            .unwrap_or_else(rcl::MTSafeFn::rcl_action_server_get_default_options);
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

        let server = Self {
            data: Arc::new(ActionServerData {
                server,
                node,
                results: Mutex::new(BTreeMap::new()),
            }),
            clock,
        };

        Ok(server)
    }

    pub fn try_recv_goal_request(
        &mut self,
    ) -> RecvResult<(rcl::rmw_request_id_t, SendGoalServiceRequest<T>), ()> {
        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut request: SendGoalServiceRequest<T> = unsafe { MaybeUninit::zeroed().assume_init() };
        let result = {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_action_take_goal_request(
                &self.data.server,
                &mut header,
                &mut request as *const _ as *mut _,
            )
        };

        match result {
            Ok(()) => RecvResult::Ok((header, request)),
            Err(RCLActionError::ServerTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    pub fn try_recv_cancel_request(
        &mut self,
    ) -> RecvResult<(rcl::rmw_request_id_t, rcl_action_cancel_request_t), ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut request: rcl_action_cancel_request_t =
            rcl::MTSafeFn::rcl_action_get_zero_initialized_cancel_request();

        match guard.rcl_action_take_cancel_request(
            &self.data.server,
            &mut header,
            &mut request as *const _ as *mut _,
        ) {
            Ok(()) => RecvResult::Ok((header, request)),
            Err(RCLActionError::ServerTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    pub fn try_recv_result_request(
        &mut self,
    ) -> RecvResult<(rcl::rmw_request_id_t, GetResultServiceRequest<T>), ()> {
        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut request: GetResultServiceRequest<T> =
            unsafe { MaybeUninit::zeroed().assume_init() };

        let take_result = {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_action_take_result_request(
                &self.data.server,
                &mut header,
                &mut request as *const _ as *mut _,
            )
        };

        match take_result {
            Ok(()) => RecvResult::Ok((header, request)),
            Err(RCLActionError::ServerTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    /// Send a response for SendGoal service, and accept the goal if `accepted` is true.
    pub(crate) fn handle_goal(
        &mut self,
        accepted: bool,
        mut header: rmw_request_id_t,
        goal_id: [u8; 16],
    ) -> Result<(), DynError> {
        let timestamp = self.get_timestamp();
        if accepted {
            self.accept_goal(goal_id, Some(timestamp))?;
        }

        // TODO: Make SendgoalServiceResponse independent of T (edit safe-drive-msg)
        type GoalResponse<T> = <<T as ActionMsg>::Goal as ActionGoal>::Response;
        let mut response = GoalResponse::<T>::new(accepted, timestamp);

        // send response to client
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_action_send_goal_response(
            unsafe { self.data.as_ptr_mut() },
            &mut header,
            &mut response as *const _ as *mut _,
        )?;

        Ok(())
    }

    pub(crate) fn accept_goal(
        &mut self,
        goal_id: [u8; 16],
        timestamp: Option<UnsafeTime>,
    ) -> Result<(), DynError> {
        let timestamp = timestamp.unwrap_or_else(|| self.get_timestamp());
        // see rcl_interfaces/action_msgs/msg/GoalInfo.msg for definition
        let mut goal_info = rcl::MTSafeFn::rcl_action_get_zero_initialized_goal_info();

        goal_info.goal_id = unique_identifier_msgs__msg__UUID { uuid: goal_id };
        goal_info.stamp.sec = timestamp.sec;
        goal_info.stamp.nanosec = timestamp.nanosec;

        let server_ptr = unsafe { self.data.as_ptr_mut() };
        rcl_action_accept_new_goal(server_ptr, &goal_info)?;
        update_goal_status(server_ptr, &[goal_id], GoalStatus::Accepted)?;

        Ok(())
    }

    pub fn try_recv_data(&mut self) -> Result<(), DynError> {
        let _ = self.try_recv_result_request();
        Ok(())
    }

    pub(crate) fn create_goal_handle(&self, goal_id: [u8; 16]) -> GoalHandle<T> {
        GoalHandle::new(goal_id, self.data.clone())
    }

    fn get_timestamp(&mut self) -> UnsafeTime {
        let now_nanosec = self.clock.get_now().unwrap();
        let now_sec = now_nanosec / 10_i64.pow(9);
        UnsafeTime {
            sec: now_sec as i32,
            nanosec: (now_nanosec - now_sec * 10_i64.pow(9)) as u32,
        }
    }
}

impl<T: ActionMsg> Drop for Server<T> {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_action_server_fini(unsafe { self.data.as_ptr_mut() }, unsafe {
            self.data.node.as_ptr_mut()
        });
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

fn rcl_action_accept_new_goal(
    server: *mut rcl_action_server_t,
    goal_info: &action_msgs__msg__GoalInfo,
) -> Result<*mut rcl_action_goal_handle_t, rcl::rcutils_error_string_t> {
    let goal_handle = {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_action_accept_new_goal(server, goal_info)
    };
    if goal_handle.is_null() {
        let msg = unsafe { rcl::rcutils_get_error_string() };
        return Err(msg);
    }

    Ok(goal_handle)
}
