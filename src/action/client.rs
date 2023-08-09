use std::{ffi::CString, marker::PhantomData, mem::MaybeUninit, sync::Arc, time::Duration};

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
    rcl,
    selector::Selector,
    PhantomUnsync, RecvResult,
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

pub(crate) struct ClientData {
    pub(crate) client: rcl::rcl_action_client_t,
    pub(crate) node: Arc<Node>,
}

impl Drop for ClientData {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_action_client_fini(&mut self.client, unsafe { self.node.as_ptr_mut() });
    }
}

unsafe impl Sync for ClientData {}
unsafe impl Send for ClientData {}

/// An action client.
pub struct Client<T: ActionMsg> {
    data: Arc<ClientData>,
    _phantom: PhantomData<T>,
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
            .unwrap_or_else(rcl::MTSafeFn::rcl_action_client_get_default_options);
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
            data: Arc::new(ClientData { client, node }),
            _phantom: Default::default(),
        })
    }

    pub fn is_server_available(&self) -> RCLActionResult<bool> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut is_available = false;
        match guard.rcl_action_server_is_available(
            self.data.node.as_ptr(),
            &self.data.client,
            &mut is_available as *mut _,
        ) {
            Ok(()) => Ok(is_available),
            Err(RCLActionError::RCLError(RCLError::NodeInvalid)) => {
                // TODO: soft failure in case of shutdown context
                eprintln!("Invalid node (the shutdown has started?)");
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }

    // Send a goal request to the server. the UUID are automatically attached.
    // pub fn send_goal<GR>(&mut self, goal: <T as ActionMsg>::Goal, callback: GR) -> Result<(), DynError>
    // where GR: FnOnce(SendGoalServiceResponse<T>) {
    //     let request = <T as ActionMsg>::new_goal_request(

    //     goal, uuid);
    //         self.send_goal_request(&request,Box::new(callback) )

    // )

    /// Send a goal request to the server with given uuid. the uuid can be any 16-bit slice [u8; 16] i.e. does not have to
    /// strictly conform to the UUID v4 standard.
    pub fn send_goal_with_uuid(
        self,
        goal: <T as ActionMsg>::GoalContent,
        uuid: [u8; 16],
    ) -> Result<ClientGoalRecv<T>, DynError> {
        let request = <T as ActionMsg>::new_goal_request(goal, uuid);
        self.send_goal_request(&request)
    }

    /// Send a goal request.
    pub fn send_goal_request(
        self,
        data: &SendGoalServiceRequest<T>,
    ) -> Result<ClientGoalRecv<T>, DynError> {
        let mut seq: i64 = 0;
        rcl::MTSafeFn::rcl_action_send_goal_request(
            &self.data.client,
            data as *const _ as _,
            &mut seq,
        )?;

        Ok(ClientGoalRecv {
            inner: ClientRecv::new(self.data),
            seq,
        })
    }

    /// Send a result request to the server.
    pub fn send_result_request(
        self,
        data: &GetResultServiceRequest<T>,
    ) -> Result<ClientResultRecv<T>, DynError> {
        let mut seq: i64 = 0;
        rcl::MTSafeFn::rcl_action_send_result_request(
            &self.data.client,
            data as *const GetResultServiceRequest<T> as _,
            &mut seq,
        )?;

        Ok(ClientResultRecv {
            inner: ClientRecv::new(self.data),
            seq,
        })
    }

    /// Send a cancel request.
    pub fn send_cancel_request(
        self,
        request: &CancelGoalRequest,
    ) -> Result<ClientCancelRecv<T>, DynError> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut seq: i64 = 0;
        guard.rcl_action_send_cancel_request(
            &self.data.client,
            request as *const _ as _,
            &mut seq,
        )?;

        Ok(ClientCancelRecv {
            inner: ClientRecv::new(self.data),
            seq,
        })
    }

    /// Takes a feedback for the goal.
    pub fn try_recv_feedback(&self) -> RecvResult<<T as ActionMsg>::Feedback, ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut feedback: <T as ActionMsg>::Feedback =
            unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_feedback(&self.data.client, &mut feedback as *const _ as *mut _)
        {
            Ok(()) => RecvResult::Ok(feedback),
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    /// Wait until the client receives a feedback message or the duration `t` elapses.
    pub fn recv_feedback_timeout(
        &self,
        t: Duration,
        selector: &mut Selector,
    ) -> RecvResult<<T as ActionMsg>::Feedback, ()> {
        selector.add_action_client(&self.data.client);
        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv_feedback(),
            Ok(false) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e),
        }
    }

    // Takes a status message for all the ongoing goals.
    // TODO: maybe return status_array.status_list. could it be cloned?
    pub fn try_recv_status(&self) -> RecvResult<GoalStatusArray, ()> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut status_array: GoalStatusArray = unsafe { MaybeUninit::zeroed().assume_init() };
        match guard
            .rcl_action_take_status(&self.data.client, &mut status_array as *const _ as *mut _)
        {
            Ok(()) => RecvResult::Ok(status_array),
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    /// Wait until the client receives a status message or the duration `t` elapses.
    pub fn recv_status_timeout(
        &self,
        t: Duration,
        selector: &mut Selector,
    ) -> RecvResult<GoalStatusArray, ()> {
        selector.add_action_client(&self.data.client);
        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv_status(),
            Ok(false) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e),
        }
    }
}

#[derive(Clone)]
pub struct ClientRecv<T> {
    data: Arc<ClientData>,
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T: ActionMsg> ClientRecv<T> {
    fn new(data: Arc<ClientData>) -> Self {
        Self {
            data,
            _phantom: Default::default(),
            _unsync: Default::default(),
        }
    }
}

#[derive(Clone)]
pub struct ClientGoalRecv<T> {
    inner: ClientRecv<T>,
    seq: i64,
}

impl<T: ActionMsg> ClientGoalRecv<T> {
    pub fn try_recv(
        self,
    ) -> RecvResult<(Client<T>, SendGoalServiceResponse<T>, rcl::rmw_request_id_t), Self> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut response: SendGoalServiceResponse<T> =
            unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_goal_response(
            &self.inner.data.client,
            &mut header,
            &mut response as *const _ as *mut _,
        ) {
            Ok(()) => {
                if header.sequence_number == self.seq {
                    let client = Client {
                        data: self.inner.data,
                        _phantom: Default::default(),
                    };
                    RecvResult::Ok((client, response, header))
                } else {
                    RecvResult::RetryLater(self)
                }
            }
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    /// Wait until the client receives a response or the duration `t` elapses.
    pub fn recv_timeout(
        self,
        t: Duration,
        selector: &mut Selector,
    ) -> RecvResult<(Client<T>, SendGoalServiceResponse<T>, rcl::rmw_request_id_t), Self> {
        selector.add_action_client(&self.inner.data.client);

        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv(),
            Ok(false) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e),
        }
    }
}

#[derive(Clone)]
pub struct ClientCancelRecv<T> {
    inner: ClientRecv<T>,
    seq: i64,
}

impl<T: ActionMsg> ClientCancelRecv<T> {
    pub fn try_recv(
        self,
    ) -> RecvResult<(Client<T>, CancelGoalResponse, rcl::rmw_request_id_t), Self> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut response: CancelGoalResponse = unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_cancel_response(
            &self.inner.data.client,
            &mut header,
            &mut response as *const _ as *mut _,
        ) {
            Ok(()) => {
                if header.sequence_number == self.seq {
                    let client = Client {
                        data: self.inner.data,
                        _phantom: Default::default(),
                    };
                    RecvResult::Ok((client, response, header))
                } else {
                    RecvResult::RetryLater(self)
                }
            }
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    /// Wait until the client receives a response or the duration `t` elapses.
    pub fn recv_timeout(
        self,
        t: Duration,
        selector: &mut Selector,
    ) -> RecvResult<(Client<T>, CancelGoalResponse, rcl::rmw_request_id_t), Self> {
        selector.add_action_client(&self.inner.data.client);

        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv(),
            Ok(false) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e),
        }
    }
}

#[derive(Clone)]
pub struct ClientResultRecv<T> {
    inner: ClientRecv<T>,
    seq: i64,
}

impl<T: ActionMsg> ClientResultRecv<T> {
    pub fn try_recv(
        self,
    ) -> RecvResult<
        (
            Client<T>,
            GetResultServiceResponse<T>,
            rcl::rmw_request_id_t,
        ),
        Self,
    > {
        let guard = rcl::MT_UNSAFE_FN.lock();

        let mut header = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut response = unsafe { MaybeUninit::zeroed().assume_init() };
        match guard.rcl_action_take_result_response(
            &self.inner.data.client,
            &mut header,
            &mut response as *const _ as *mut _,
        ) {
            Ok(()) => {
                if header.sequence_number == self.seq {
                    let client = Client {
                        data: self.inner.data,
                        _phantom: Default::default(),
                    };
                    RecvResult::Ok((client, response, header))
                } else {
                    RecvResult::RetryLater(self)
                }
            }
            Err(RCLActionError::ClientTakeFailed) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    /// Wait until the client receives a response or the duration `t` elapses.
    pub fn recv_timeout(
        self,
        t: Duration,
        selector: &mut Selector,
    ) -> RecvResult<
        (
            Client<T>,
            GetResultServiceResponse<T>,
            rcl::rmw_request_id_t,
        ),
        Self,
    > {
        selector.add_action_client(&self.inner.data.client);

        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv(),
            Ok(false) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e),
        }
    }
}
