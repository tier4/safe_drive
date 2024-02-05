use pin_project::{pin_project, pinned_drop};
use std::f32::consts::E;
use std::future::Future;
use std::pin::Pin;
use std::{
    ffi::CString, marker::PhantomData, mem::MaybeUninit, sync::Arc, task::Poll, time::Duration,
};

use crate::{
    error::{DynError, RCLActionError, RCLActionResult, RCLError},
    get_allocator, is_halt,
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
    selector::{
        async_selector::{self, SELECTOR},
        CallbackResult, Selector,
    },
    signal_handler::Signaled,
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
        if crate::is_halt() {
            return Err(Signaled.into());
        }

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
        match rcl_action_take_feedback::<T>(&self.data.client) {
            Ok(feedback) => RecvResult::Ok(feedback),
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
        selector.add_action_client(self.data.clone(), None, None, None, None, None);
        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv_feedback(),
            Ok(false) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e),
        }
    }

    // Asynchronously receive a feedback message.
    pub async fn recv_feedback(self) -> Result<(Self, <T as ActionMsg>::Feedback), DynError> {
        AsyncFeedbackReceiver {
            data: self.data.clone(),
            is_waiting: false,
            _phantom: Default::default(),
        }
        .await
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
        selector.add_action_client(self.data.clone(), None, None, None, None, None);
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
    pub(crate) inner: ClientRecv<T>,
    seq: i64,
}

impl<T: ActionMsg> ClientGoalRecv<T> {
    pub fn try_recv(
        self,
    ) -> RecvResult<(Client<T>, SendGoalServiceResponse<T>, rcl::rmw_request_id_t), Self> {
        match rcl_action_take_goal_response::<T>(&self.inner.data.client) {
            Ok((response, header)) => {
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
        selector.add_action_client(self.inner.data.clone(), None, None, None, None, None);

        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv(),
            Ok(false) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e),
        }
    }

    pub fn recv(self) -> AsyncGoalReceiver<T> {
        AsyncGoalReceiver {
            client: self,
            is_waiting: false,
        }
    }
}

#[pin_project(PinnedDrop)]
pub struct AsyncGoalReceiver<T: ActionMsg> {
    client: ClientGoalRecv<T>,
    is_waiting: bool,
}

impl<T: ActionMsg> AsyncGoalReceiver<T> {
    pub fn give_up(self) -> Client<T> {
        Client {
            data: self.client.inner.data.clone(),
            _phantom: Default::default(),
        }
    }
}

#[pinned_drop]
impl<T: ActionMsg> PinnedDrop for AsyncGoalReceiver<T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.client.inner.data.node.context,
                async_selector::Command::RemoveActionClient(self.client.inner.data.clone()),
            );
        }
    }
}

impl<T: ActionMsg> Future for AsyncGoalReceiver<T> {
    type Output = Result<(Client<T>, SendGoalServiceResponse<T>, rcl::rmw_request_id_t), DynError>;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();
        *this.is_waiting = false;

        match rcl_action_take_goal_response::<T>(&this.client.inner.data.client) {
            Ok((response, header)) => {
                if header.sequence_number == this.client.seq {
                    let client = Client {
                        data: this.client.inner.data.clone(),
                        _phantom: Default::default(),
                    };
                    return Poll::Ready(Ok((client, response, header)));
                }
            }
            Err(RCLActionError::ClientTakeFailed) => {}
            Err(e) => return Poll::Ready(Err(e.into())),
        }

        let mut waker = Some(cx.waker().clone());
        let mut guard = SELECTOR.lock();

        match guard.send_command(
            &this.client.inner.data.node.context,
            async_selector::Command::ActionClient {
                data: this.client.inner.data.clone(),
                feedback: Box::new(|| CallbackResult::Ok),
                status: Box::new(|| CallbackResult::Ok),
                goal: Box::new(move || {
                    let w = waker.take().unwrap();
                    w.wake();
                    CallbackResult::Remove
                }),
                cancel: Box::new(|| CallbackResult::Ok),
                result: Box::new(|| CallbackResult::Ok),
            },
        ) {
            Ok(_) => {
                *this.is_waiting = true;
                Poll::Pending
            }
            Err(e) => Poll::Ready(Err(e)),
        }
    }
}

#[derive(Clone)]
pub struct ClientCancelRecv<T> {
    pub(crate) inner: ClientRecv<T>,
    seq: i64,
}

impl<T: ActionMsg> ClientCancelRecv<T> {
    pub fn try_recv(
        self,
    ) -> RecvResult<(Client<T>, CancelGoalResponse, rcl::rmw_request_id_t), Self> {
        match rcl_action_take_cancel_response(&self.inner.data.client) {
            Ok((response, header)) => {
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
        selector.add_action_client(self.inner.data.clone(), None, None, None, None, None);

        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv(),
            Ok(false) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e),
        }
    }

    pub async fn recv(
        self,
    ) -> Result<(Client<T>, CancelGoalResponse, rcl::rmw_request_id_t), DynError> {
        AsyncCancelReceiver {
            client: self,
            is_waiting: false,
        }
        .await
    }
}

#[pin_project(PinnedDrop)]
pub struct AsyncCancelReceiver<T: ActionMsg> {
    client: ClientCancelRecv<T>,
    is_waiting: bool,
}

impl<T: ActionMsg> AsyncCancelReceiver<T> {
    pub fn give_up(self) -> Client<T> {
        Client {
            data: self.client.inner.data.clone(),
            _phantom: Default::default(),
        }
    }
}

#[pinned_drop]
impl<T: ActionMsg> PinnedDrop for AsyncCancelReceiver<T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.client.inner.data.node.context,
                async_selector::Command::RemoveActionClient(self.client.inner.data.clone()),
            );
        }
    }
}

impl<T: ActionMsg> Future for AsyncCancelReceiver<T> {
    type Output = Result<(Client<T>, CancelGoalResponse, rcl::rmw_request_id_t), DynError>;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();
        *this.is_waiting = false;

        match rcl_action_take_cancel_response(&this.client.inner.data.client) {
            Ok((response, header)) => {
                if header.sequence_number == this.client.seq {
                    let client = Client {
                        data: this.client.inner.data.clone(),
                        _phantom: Default::default(),
                    };
                    return Poll::Ready(Ok((client, response, header)));
                }
            }
            Err(RCLActionError::ClientTakeFailed) => {}
            Err(e) => return Poll::Ready(Err(e.into())),
        }

        let mut waker = Some(cx.waker().clone());
        let mut guard = SELECTOR.lock();

        match guard.send_command(
            &this.client.inner.data.node.context,
            async_selector::Command::ActionClient {
                data: this.client.inner.data.clone(),
                feedback: Box::new(|| CallbackResult::Ok),
                status: Box::new(|| CallbackResult::Ok),
                goal: Box::new(|| CallbackResult::Ok),
                cancel: Box::new(move || {
                    let w = waker.take().unwrap();
                    w.wake();
                    CallbackResult::Remove
                }),
                result: Box::new(|| CallbackResult::Ok),
            },
        ) {
            Ok(_) => {
                *this.is_waiting = true;
                Poll::Pending
            }
            Err(e) => Poll::Ready(Err(e)),
        }
    }
}

#[derive(Clone)]
pub struct ClientResultRecv<T> {
    pub(crate) inner: ClientRecv<T>,
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
        match rcl_action_take_result_response::<T>(&self.inner.data.client) {
            Ok((response, header)) => {
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
        selector.add_action_client(self.inner.data.clone(), None, None, None, None, None);

        match selector.wait_timeout(t) {
            Ok(true) => self.try_recv(),
            Ok(false) => RecvResult::RetryLater(self),
            Err(e) => RecvResult::Err(e),
        }
    }

    pub fn recv(self) -> AsyncResultReceiver<T> {
        AsyncResultReceiver {
            client: self,
            is_waiting: false,
        }
    }
}

#[pin_project(PinnedDrop)]
pub struct AsyncResultReceiver<T: ActionMsg> {
    client: ClientResultRecv<T>,
    is_waiting: bool,
}

impl<T: ActionMsg> AsyncResultReceiver<T> {
    pub fn give_up(self) -> Client<T> {
        Client {
            data: self.client.inner.data.clone(),
            _phantom: Default::default(),
        }
    }
}

#[pinned_drop]
impl<T: ActionMsg> PinnedDrop for AsyncResultReceiver<T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.client.inner.data.node.context,
                async_selector::Command::RemoveActionClient(self.client.inner.data.clone()),
            );
        }
    }
}

impl<T: ActionMsg> Future for AsyncResultReceiver<T> {
    type Output = Result<
        (
            Client<T>,
            GetResultServiceResponse<T>,
            rcl::rmw_request_id_t,
        ),
        DynError,
    >;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();
        *this.is_waiting = false;

        match rcl_action_take_result_response::<T>(&this.client.inner.data.client) {
            Ok((response, header)) => {
                if header.sequence_number == this.client.seq {
                    let client = Client {
                        data: this.client.inner.data.clone(),
                        _phantom: Default::default(),
                    };
                    return Poll::Ready(Ok((client, response, header)));
                }
            }
            Err(RCLActionError::ClientTakeFailed) => {}
            Err(e) => return Poll::Ready(Err(e.into())),
        }

        let mut waker = Some(cx.waker().clone());
        let mut guard = SELECTOR.lock();

        match guard.send_command(
            &this.client.inner.data.node.context,
            async_selector::Command::ActionClient {
                data: this.client.inner.data.clone(),
                feedback: Box::new(|| CallbackResult::Ok),
                status: Box::new(|| CallbackResult::Ok),
                goal: Box::new(|| CallbackResult::Ok),
                cancel: Box::new(|| CallbackResult::Ok),
                result: Box::new(move || {
                    let w = waker.take().unwrap();
                    w.wake();
                    CallbackResult::Remove
                }),
            },
        ) {
            Ok(_) => {
                *this.is_waiting = true;
                Poll::Pending
            }
            Err(e) => Poll::Ready(Err(e)),
        }
    }
}

#[pin_project(PinnedDrop)]
pub struct AsyncFeedbackReceiver<T: ActionMsg> {
    data: Arc<ClientData>,
    is_waiting: bool,
    _phantom: PhantomData<T>,
}

impl<T: ActionMsg> AsyncFeedbackReceiver<T> {
    pub fn give_up(self) -> Client<T> {
        Client {
            data: self.data.clone(),
            _phantom: Default::default(),
        }
    }
}

#[pinned_drop]
impl<T: ActionMsg> PinnedDrop for AsyncFeedbackReceiver<T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.data.node.context,
                async_selector::Command::RemoveActionClient(self.data.clone()),
            );
        }
    }
}

impl<T: ActionMsg> Future for AsyncFeedbackReceiver<T> {
    type Output = Result<(Client<T>, <T as ActionMsg>::Feedback), DynError>;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();
        *this.is_waiting = false;

        match rcl_action_take_feedback::<T>(&this.data.client) {
            Ok(feedback) => {
                let client = Client {
                    data: this.data.clone(),
                    _phantom: Default::default(),
                };
                return Poll::Ready(Ok((client, feedback)));
            }
            Err(RCLActionError::ClientTakeFailed) => {}
            Err(e) => return Poll::Ready(Err(e.into())),
        }

        let mut waker = Some(cx.waker().clone());
        let mut guard = SELECTOR.lock();

        match guard.send_command(
            &this.data.node.context,
            async_selector::Command::ActionClient {
                data: this.data.clone(),
                feedback: Box::new(move || {
                    let w = waker.take().unwrap();
                    w.wake();
                    CallbackResult::Remove
                }),
                status: Box::new(|| CallbackResult::Ok),
                goal: Box::new(|| CallbackResult::Ok),
                cancel: Box::new(|| CallbackResult::Ok),
                result: Box::new(|| CallbackResult::Ok),
            },
        ) {
            Ok(_) => {
                *this.is_waiting = true;
                Poll::Pending
            }
            Err(e) => Poll::Ready(Err(e)),
        }
    }
}

fn rcl_action_take_goal_response<T>(
    client: &rcl::rcl_action_client_t,
) -> RCLActionResult<(SendGoalServiceResponse<T>, rcl::rmw_request_id_t)>
where
    T: ActionMsg,
{
    let guard = rcl::MT_UNSAFE_FN.lock();

    let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
    let mut response: SendGoalServiceResponse<T> = unsafe { MaybeUninit::zeroed().assume_init() };
    guard.rcl_action_take_goal_response(
        client,
        &mut header,
        &mut response as *const _ as *mut _,
    )?;

    Ok((response, header))
}

fn rcl_action_take_cancel_response(
    client: &rcl::rcl_action_client_t,
) -> RCLActionResult<(CancelGoalResponse, rcl::rmw_request_id_t)> {
    let guard = rcl::MT_UNSAFE_FN.lock();

    let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
    let mut response: CancelGoalResponse = unsafe { MaybeUninit::zeroed().assume_init() };
    guard.rcl_action_take_cancel_response(
        client,
        &mut header,
        &mut response as *const _ as *mut _,
    )?;

    Ok((response, header))
}

fn rcl_action_take_result_response<T>(
    client: &rcl::rcl_action_client_t,
) -> RCLActionResult<(GetResultServiceResponse<T>, rcl::rmw_request_id_t)>
where
    T: ActionMsg,
{
    let guard = rcl::MT_UNSAFE_FN.lock();

    let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
    let mut response: GetResultServiceResponse<T> = unsafe { MaybeUninit::zeroed().assume_init() };
    guard.rcl_action_take_result_response(
        client,
        &mut header,
        &mut response as *const _ as *mut _,
    )?;

    Ok((response, header))
}

fn rcl_action_take_feedback<T>(client: &rcl::rcl_action_client_t) -> RCLActionResult<T::Feedback>
where
    T: ActionMsg,
{
    let guard = rcl::MT_UNSAFE_FN.lock();

    let mut feedback: <T as ActionMsg>::Feedback = unsafe { MaybeUninit::zeroed().assume_init() };
    guard.rcl_action_take_feedback(client, &mut feedback as *const _ as *mut _)?;

    Ok(feedback)
}
