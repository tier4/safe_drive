use std::{collections::BTreeMap, ffi::CString, mem::MaybeUninit, sync::Arc};

use crate::{
    error::{DynError, RCLActionError, RCLActionResult, RCLError},
    get_allocator,
    msg::{
        interfaces::action_msgs::{
            msg::GoalStatusArray,
            srv::{CancelGoalRequest, CancelGoalResponse},
        },
        ActionMsg,
    },
    node::Node,
    qos::Profile,
    rcl, RecvResult,
};

use super::{
    GetResultServiceRequest, GetResultServiceResponse, SendGoalServiceRequest,
    SendGoalServiceResponse,
};

pub struct ClientQosOption {
    goal_service: Profile,
    result_service: Profile,
    cancel_service: Profile,
    feedback_topic: Profile,
    status_topic: Profile,
}

impl From<ClientQosOption> for rcl::rcl_action_client_options_t {
    fn from(opts: ClientQosOption) -> Self {
        rcl::rcl_action_client_options_t {
            goal_service_qos: (&opts.goal_service).into(),
            result_service_qos: (&opts.result_service).into(),
            cancel_service_qos: (&opts.cancel_service).into(),
            feedback_topic_qos: (&opts.feedback_topic).into(),
            status_topic_qos: (&opts.status_topic).into(),
            allocator: get_allocator(),
        }
    }
}

/// An action client.
pub struct Client<T: ActionMsg> {
    client: rcl::rcl_action_client_t,
    node: Arc<Node>,

    goal_response_callbacks: BTreeMap<i64, Box<dyn FnOnce(SendGoalServiceResponse<T>)>>,
    cancel_response_callbacks: BTreeMap<i64, Box<dyn FnOnce(CancelGoalResponse)>>,
    result_response_callbacks: BTreeMap<i64, Box<dyn FnOnce(GetResultServiceResponse<T>)>>,
}

impl<T> Client<T>
where
    T: ActionMsg,
{
    // Create a client.
    pub fn new(
        node: Arc<Node>,
        action_name: &str,
        qos: Option<ClientQosOption>,
    ) -> RCLActionResult<Self> {
        let mut client = rcl::MTSafeFn::rcl_action_get_zero_initialized_client();
        let options = qos
            .map(rcl::rcl_action_client_options_t::from)
            .unwrap_or(rcl::MTSafeFn::rcl_action_client_get_default_options());
        let action_name = CString::new(action_name).unwrap_or_default();

        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_action_client_init(
                &mut client,
                unsafe { node.as_ptr_mut() },
                T::type_support(),
                action_name.as_ptr(),
                &options,
            )?;
        }

        Ok(Self {
            client,
            node,
            goal_response_callbacks: Default::default(),
            cancel_response_callbacks: Default::default(),
            result_response_callbacks: Default::default(),
        })
    }

    pub fn is_server_available(&self) -> RCLActionResult<bool> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut is_available = false;
        match guard.rcl_action_server_is_available(
            self.node.as_ptr(),
            &self.client,
            &mut is_available as *mut _,
        ) {
            Ok(()) => Ok(is_available),
            Err(RCLActionError::RCLError(RCLError::NodeInvalid)) => {
                // TODO: soft failure in case of shutdown context
                eprintln!("Invalid node (the shutdown has started?)");
                Ok(false)
            }
            Err(e) => Err(e.into()),
        }
    }

    // Send a goal request to the server. the UUID are automatically attached.
    // pub fn send_goal(&mut self, goal: &<<T as ActionMsg>::Goal as ServiceMsg>

    // )

    /// Send a goal request to the server with given uuid. the uuid can be any 16-bit slice [u8; 16] i.e. does not have to
    /// strictly conform to the UUID v4 standard.
    pub fn send_goal_with_uuid<GR>(
        &mut self,
        goal: <T as ActionMsg>::GoalContent,
        uuid: [u8; 16],
        callback: GR,
    ) -> Result<(), DynError>
    where
        GR: FnOnce(SendGoalServiceResponse<T>) + 'static,
    {
        let request = <T as ActionMsg>::new_goal_request(goal, uuid);
        let boxed = Box::new(callback);
        self.send_goal_request(&request, boxed)
    }

    /// Send a goal request.
    pub fn send_goal_request(
        &mut self,
        data: &SendGoalServiceRequest<T>,
        callback: Box<dyn FnOnce(SendGoalServiceResponse<T>)>,
    ) -> Result<(), DynError> {
        // TODO: use mutex?
        // TODO: callbacks are FnMut? Fn? FnOnce?

        let mut seq: i64 = 0;
        rcl::MTSafeFn::rcl_action_send_goal_request(
            &self.client,
            data as *const SendGoalServiceRequest<T> as _,
            &mut seq,
        )?;

        if self.goal_response_callbacks.contains_key(&seq) {
            Err(format!(
                "A goal callback with sequence number {} already exists",
                seq
            )
            .into())
        } else {
            self.goal_response_callbacks.insert(seq, callback);
            Ok(())
        }
    }

    // TODO: what should be the second type argument for RecvResult
    // TODO: return Result<()>?
    pub fn try_recv_goal_response(&mut self) -> RecvResult<(), ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut response: SendGoalServiceResponse<T> =
            unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_goal_response(
            &self.client,
            &mut header,
            &mut response as *const _ as *mut _,
        ) {
            Ok(()) => {
                let seq = header.sequence_number;
                match self.goal_response_callbacks.remove(&seq) {
                    Some(callback) => callback(response),
                    None => {
                        return RecvResult::Err(
                            format!(
                                "The goal callback with sequence number {} was not found",
                                seq
                            )
                            .into(),
                        );
                    }
                }

                RecvResult::Ok(())
            }
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    pub fn send_result_request(
        &mut self,
        data: &GetResultServiceRequest<T>,
        callback: Box<dyn FnOnce(GetResultServiceResponse<T>)>,
    ) -> Result<(), DynError> {
        // TODO: use mutex?

        let mut seq: i64 = 0;
        rcl::MTSafeFn::rcl_action_send_result_request(
            &self.client,
            data as *const GetResultServiceRequest<T> as _,
            &mut seq,
        )?;

        if self.result_response_callbacks.contains_key(&seq) {
            Err(format!(
                "A result callback with sequence number {} already exists",
                seq
            )
            .into())
        } else {
            self.result_response_callbacks.insert(seq, callback);
            Ok(())
        }
    }

    // Takes a result for the goal.
    pub fn try_recv_result_response(&mut self) -> RecvResult<(), ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut response: GetResultServiceResponse<T> =
            unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_result_response(
            &self.client,
            &mut header,
            &mut response as *const _ as *mut _,
        ) {
            Ok(()) => {
                let seq = header.sequence_number;
                match self.result_response_callbacks.remove(&seq) {
                    Some(callback) => callback(response),
                    None => {
                        return RecvResult::Err(
                            format!(
                                "The goal callback with sequence number {} was not found",
                                seq
                            )
                            .into(),
                        );
                    }
                }

                RecvResult::Ok(())
            }
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    /// Send a cancel request.
    pub fn send_cancel_request(
        &mut self,
        request: &CancelGoalRequest,
        callback: Box<dyn FnOnce(CancelGoalResponse)>,
    ) -> Result<(), DynError> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut seq: i64 = 0;
        guard.rcl_action_send_cancel_request(&self.client, request as *const _ as _, &mut seq)?;

        if self.cancel_response_callbacks.contains_key(&seq) {
            Err(format!(
                "A cancel callback with sequence number {} already exists",
                seq
            )
            .into())
        } else {
            self.cancel_response_callbacks.insert(seq, callback);
            Ok(())
        }
    }

    /// Takes a response for a cancel request.
    pub fn try_recv_cancel_response(&mut self) -> RecvResult<(), ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut response: CancelGoalResponse = unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_cancel_response(
            &self.client,
            &mut header,
            &mut response as *const _ as *mut _,
        ) {
            Ok(()) => {
                let seq = header.sequence_number;
                match self.cancel_response_callbacks.remove(&seq) {
                    Some(callback) => callback(response),
                    None => {
                        return RecvResult::Err(
                            format!(
                                "The cancel goal callback with sequence number {} was not found",
                                seq
                            )
                            .into(),
                        );
                    }
                }

                RecvResult::Ok(())
            }
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    // Takes a feedback for the goal.
    pub fn try_recv_feedback(&self) -> RecvResult<<T as ActionMsg>::Feedback, ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut feedback: <T as ActionMsg>::Feedback =
            unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_feedback(&self.client, &mut feedback as *const _ as *mut _) {
            Ok(()) => RecvResult::Ok(feedback),
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    // Takes a status message for all the ongoing goals.
    // TODO: maybe return status_array.status_list. could it be cloned?
    pub fn try_recv_status(&self) -> RecvResult<GoalStatusArray, ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut status_array: GoalStatusArray = unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_status(&self.client, &mut status_array as *const _ as *mut _) {
            Ok(()) => RecvResult::Ok(status_array),
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }
}

impl<T: ActionMsg> Drop for Client<T> {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_action_client_fini(&mut self.client, unsafe { self.node.as_ptr_mut() });
    }
}
