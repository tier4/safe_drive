use std::{ffi::CString, mem::MaybeUninit, sync::Arc, time::Duration};

use crate::{
    clock::Clock,
    error::{RCLActionError, RCLActionResult},
    get_allocator,
    msg::{builtin_interfaces, ActionGoal, ActionMsg, GetUUID, GoalResponse},
    node::Node,
    qos::Profile,
    rcl::{self, rcutils_get_error_string, unique_identifier_msgs__msg__UUID},
    RecvResult,
};

use super::SendGoalServiceRequest;

pub struct ServerQosOption {
    goal_service: Profile,
    result_service: Profile,
    cancel_service: Profile,
    feedback_topic: Profile,
    status_topic: Profile,
    result_timeout: Duration,
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
    goal_request_callback: Box<dyn Fn(&SendGoalServiceRequest<T>) -> bool>,
}

impl<T> Server<T>
where
    T: ActionMsg,
{
    /// Create a server.
    pub fn new<GR>(
        node: Arc<Node>,
        action_name: &str,
        qos: Option<ServerQosOption>,
        goal_request_callback: GR,
    ) -> RCLActionResult<Self>
    where
        GR: Fn(&SendGoalServiceRequest<T>) -> bool + 'static,
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

        Ok(Self {
            server,
            node,
            clock,
            goal_request_callback: Box::new(goal_request_callback),
        })
    }

    pub fn try_recv_goal_request(&mut self) -> RecvResult<(), ()> {
        assert!(rcl::MTSafeFn::rcl_clock_valid(&mut self.clock.clock));

        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut request: SendGoalServiceRequest<T> = unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_goal_request(
            &self.server,
            &mut header,
            &mut request as *const _ as *mut _,
        ) {
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
                let accepted = callback(&request);

                if accepted {
                    // see rcl_interfaces/action_msgs/msg/GoalInfo.msg for definition
                    let mut goal_info = rcl::MTSafeFn::rcl_action_get_zero_initialized_goal_info();

                    let uuid = request.get_uuid().clone();
                    goal_info.goal_id = unique_identifier_msgs__msg__UUID { uuid };

                    goal_info.stamp.sec = (now_nanosec / 10_i64.pow(9)) as i32;
                    goal_info.stamp.nanosec = (now_nanosec - now_sec * 10_i64.pow(9)) as u32;

                    assert!(rcl::MTSafeFn::rcl_clock_valid(&mut self.clock.clock));
                    println!("{:?}", self.clock.clock.get_now); // this access makes difference
                    println!("{:?}", self.clock.clock.type_); // this access makes difference

                    let goal_handle =
                        guard.rcl_action_accept_new_goal(&mut self.server, &goal_info);
                    if goal_handle.is_null() {
                        let msg = unsafe { rcutils_get_error_string() };
                        return RecvResult::Err(format!("Failed to accept new goal: {msg}").into());
                    }
                }

                // TODO: Make SendgoalServiceResponse independent of T (edit safe-drive-msg)
                // SendGoal
                type GoalResponse<T> = <<T as ActionMsg>::Goal as ActionGoal>::Response;

                let mut response = GoalResponse::<T>::new(accepted, stamp);
                // let mut response = SendGoalServiceResponse { accepted, stamp };

                // send response to client
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

    // pub fn try_recv_goal_
}

impl<T: ActionMsg> Drop for Server<T> {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_action_server_fini(&mut self.server, unsafe { self.node.as_ptr_mut() });
    }
}
