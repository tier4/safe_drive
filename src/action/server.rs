use parking_lot::Mutex;
use pin_project::{pin_project, pinned_drop};
use std::future::Future;
use std::marker::PhantomData;
use std::{
    collections::BTreeMap, ffi::CString, mem::MaybeUninit, pin::Pin, sync::Arc, task::Poll,
    time::Duration,
};

use crate::logger::{pr_error_in, Logger};
use crate::msg::interfaces::action_msgs::msg::GoalInfoSeq;
use crate::msg::interfaces::action_msgs::srv::{ERROR_NONE, ERROR_REJECTED};
use crate::msg::GetUUID;
use crate::rcl::action_msgs__msg__GoalInfo__Sequence;
use crate::PhantomUnsync;
use crate::{
    clock::Clock,
    error::{DynError, RCLActionError, RCLActionResult},
    get_allocator, is_halt,
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
    selector::{
        async_selector::{Command, SELECTOR},
        CallbackResult,
    },
    signal_handler::Signaled,
    RecvResult,
};

#[cfg(feature = "galactic")]
use crate::qos::galactic::*;

#[cfg(feature = "humble")]
use crate::qos::humble::*;

#[cfg(feature = "iron")]
use crate::qos::iron::*;

use super::{
    handle::GoalHandle, update_goal_status, GetResultServiceRequest, GoalStatus,
    SendGoalServiceRequest,
};
use super::{update_goal_state, GoalEvent};

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

pub(crate) struct ServerData {
    pub(crate) server: rcl::rcl_action_server_t,
    pub node: Arc<Node>,
    pub(crate) clock: Mutex<Clock>,
}

impl ServerData {
    pub(crate) unsafe fn as_ptr_mut(&self) -> *mut rcl::rcl_action_server_t {
        &self.server as *const _ as *mut _
    }
}

unsafe impl Sync for ServerData {}
unsafe impl Send for ServerData {}

impl Drop for ServerData {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_action_server_fini(unsafe { self.as_ptr_mut() }, unsafe {
            self.node.as_ptr_mut()
        });
    }
}

/// An action server.
pub struct Server<T: ActionMsg> {
    pub(crate) data: Arc<ServerData>,
    /// Once the server has completed the result for a goal, it is kept here and the result requests are responsed with the result value in this map.
    pub(crate) results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,
    pub(crate) handles: Arc<Mutex<BTreeMap<[u8; 16], *mut rcl_action_goal_handle_t>>>,
}

// FIXME: 誰がhandleのポインタを管理する？
unsafe impl<T> Send for Server<T> where T: ActionMsg {}
unsafe impl<T> Sync for Server<T> where T: ActionMsg {}

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
                unsafe { clock.as_ptr_mut() },
                T::type_support(),
                action_name.as_ptr(),
                &options,
            )?;
        }

        let server = Self {
            data: Arc::new(ServerData {
                server,
                node,
                clock: Mutex::new(clock),
            }),
            results: Arc::new(Mutex::new(BTreeMap::new())),
            handles: Arc::new(Mutex::new(BTreeMap::new())),
        };

        Ok(server)
    }

    pub fn try_recv_goal_request(
        &mut self,
    ) -> RecvResult<(ServerGoalSend<T>, SendGoalServiceRequest<T>), ()> {
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
            Ok(()) => {
                let sender = ServerGoalSend {
                    data: self.data.clone(),
                    results: self.results.clone(),
                    handles: self.handles.clone(),

                    goal_id: *request.get_uuid(),
                    request_id: header,
                    _phantom: Default::default(),
                    _unsync: Default::default(),
                };
                RecvResult::Ok((sender, request))
            }
            Err(RCLActionError::ServerTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    pub fn try_recv_cancel_request(
        &mut self,
    ) -> RecvResult<
        (
            ServerCancelSend<T>,
            rcl_action_cancel_request_t,
            Vec<GoalInfo>,
        ),
        (),
    > {
        let mut header: rcl::rmw_request_id_t = unsafe { MaybeUninit::zeroed().assume_init() };
        let mut request: rcl_action_cancel_request_t =
            rcl::MTSafeFn::rcl_action_get_zero_initialized_cancel_request();

        let guard = rcl::MT_UNSAFE_FN.lock();

        match guard.rcl_action_take_cancel_request(
            &self.data.server,
            &mut header,
            &mut request as *const _ as *mut _,
        ) {
            Ok(()) => {
                // process cancel request in advance
                let mut process_response =
                    rcl::MTSafeFn::rcl_action_get_zero_initialized_cancel_response();

                // compute which exact goals are requested to be cancelled
                // TODO: handle ERROR_UNKNOWN_GOAL_ID etc.
                if let Err(e) = guard.rcl_action_process_cancel_request(
                    unsafe { self.data.as_ptr_mut() },
                    &request,
                    &mut process_response as *const _ as *mut _,
                ) {
                    let logger = Logger::new("safe_drive");
                    pr_error_in!(
                        logger,
                        "failed to send cancel responses from action server: {}",
                        e
                    );
                    return RecvResult::Err(e.into());
                }

                let goal_seq_ptr =
                    &process_response.msg.goals_canceling as *const _ as *const GoalInfoSeq<0>;
                let candidates = unsafe { &(*goal_seq_ptr) };
                let goals = candidates
                    .iter()
                    .map(|g| GoalInfo {
                        goal_id: UUID {
                            uuid: g.goal_id.uuid,
                        },
                        stamp: g.stamp,
                    })
                    .collect::<Vec<_>>();

                // return sender
                let sender = ServerCancelSend {
                    data: self.data.clone(),
                    results: self.results.clone(),
                    handles: self.handles.clone(),
                    request_id: header,
                    _unsync: Default::default(),
                };
                RecvResult::Ok((sender, request, goals))
            }
            Err(RCLActionError::ServerTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    pub fn try_recv_result_request(
        &mut self,
    ) -> RecvResult<(ServerResultSend<T>, GetResultServiceRequest<T>), ()> {
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
            Ok(()) => {
                let sender = ServerResultSend {
                    data: self.data.clone(),
                    results: self.results.clone(),
                    request_id: header,
                    _unsync: Default::default(),
                };
                println!(
                    "uuid: {:?}, header = request_id: {:?}",
                    request.get_uuid(),
                    header
                );
                RecvResult::Ok((sender, request))
            }
            Err(RCLActionError::ServerTakeFailed) => RecvResult::RetryLater(()),
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    pub fn try_recv_data(&mut self) -> Result<(), DynError> {
        let _ = self.try_recv_result_request();
        Ok(())
    }

    pub async fn recv_goal_request(
        self,
    ) -> Result<(ServerGoalSend<T>, SendGoalServiceRequest<T>), DynError> {
        AsyncGoalReceiver {
            server: self,
            is_waiting: false,
        }
        .await
    }

    pub async fn recv_cancel_request(
        self,
    ) -> Result<(ServerCancelSend<T>, Vec<GoalInfo>), DynError> {
        AsyncCancelReceiver {
            server: self,
            is_waiting: false,
        }
        .await
    }

    pub async fn recv_result_request(
        self,
    ) -> Result<(ServerResultSend<T>, GetResultServiceRequest<T>), DynError> {
        AsyncResultReceiver {
            server: self,
            is_waiting: false,
        }
        .await
    }

    pub async fn process_result_request(self) -> Result<[u8; 16], DynError> {
        let (sender, req) = self.recv_result_request().await?;
        if let Err((_sender, e)) = sender.send(req.get_uuid()) {
            return Err(e);
        }
        Ok(*req.get_uuid())
    }
}

pub struct ServerGoalSend<T: ActionMsg> {
    data: Arc<ServerData>,
    results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,
    handles: Arc<Mutex<BTreeMap<[u8; 16], *mut rcl_action_goal_handle_t>>>,

    request_id: rmw_request_id_t,
    goal_id: [u8; 16],
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T: ActionMsg> ServerGoalSend<T> {
    /// Accept the goal request.
    pub fn accept<F>(mut self, handler: F) -> Result<Server<T>, (Self, DynError)>
    where
        F: FnOnce(GoalHandle<T>),
    {
        let timestamp = {
            let mut clock = self.data.clock.lock();
            get_timestamp(&mut clock)
        };
        match self.accept_goal(timestamp) {
            Ok(handle) => {
                let mut handles = self.handles.lock();
                handles.insert(self.goal_id, handle.handle);
                handler(handle);
            }
            Err(e) => return Err((self, e)),
        }

        let ret = self.send(true, timestamp)?;

        Ok(ret)
    }

    pub fn reject(self) -> Result<Server<T>, (Self, DynError)> {
        let timestamp = {
            let mut clock = self.data.clock.lock();
            get_timestamp(&mut clock)
        };
        self.send(false, timestamp)
    }

    /// Send a response for SendGoal service, and accept the goal if `accepted` is true.
    fn send(
        mut self,
        accepted: bool,
        timestamp: UnsafeTime,
    ) -> Result<Server<T>, (Self, DynError)> {
        // TODO: Make SendgoalServiceResponse independent of T (edit safe-drive-msg)
        type GoalResponse<T> = <<T as ActionMsg>::Goal as ActionGoal>::Response;
        let mut response = GoalResponse::<T>::new(accepted, timestamp);

        // send response to client
        let guard = rcl::MT_UNSAFE_FN.lock();
        if let Err(e) = guard.rcl_action_send_goal_response(
            unsafe { self.data.as_ptr_mut() },
            &mut self.request_id,
            &mut response as *const _ as *mut _,
        ) {
            return Err((self, e.into()));
        }

        Ok(Server {
            data: self.data,
            results: self.results,
            handles: self.handles,
        })
    }

    // pub fn handle(&self) -> GoalHandle<T> {
    //     GoalHandle::new(
    //         self.goal_id,
    //         self.goal_handle,
    //         self.data.clone(),
    //         self.results.clone(),
    //     )
    // }

    fn accept_goal(&mut self, timestamp: UnsafeTime) -> Result<GoalHandle<T>, DynError> {
        // see rcl_interfaces/action_msgs/msg/GoalInfo.msg for definition
        let mut goal_info = rcl::MTSafeFn::rcl_action_get_zero_initialized_goal_info();

        goal_info.goal_id = unique_identifier_msgs__msg__UUID { uuid: self.goal_id };
        goal_info.stamp.sec = timestamp.sec;
        goal_info.stamp.nanosec = timestamp.nanosec;

        let server_ptr = unsafe { self.data.as_ptr_mut() };
        // TODO: wrap in a Box?
        let handle_t = rcl_action_accept_new_goal(server_ptr, &goal_info)?;

        update_goal_state(handle_t, GoalEvent::Execute).unwrap();

        let handle = GoalHandle::new(
            self.goal_id,
            handle_t,
            self.data.clone(),
            self.results.clone(),
        );

        Ok(handle)
    }
}

#[pin_project(PinnedDrop)]
#[must_use]
pub struct AsyncGoalReceiver<T: ActionMsg> {
    server: Server<T>,
    is_waiting: bool,
}

impl<T: ActionMsg> Future for AsyncGoalReceiver<T> {
    type Output = Result<(ServerGoalSend<T>, SendGoalServiceRequest<T>), DynError>;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();
        *this.is_waiting = false;

        match this.server.try_recv_goal_request() {
            RecvResult::Ok((sender, request)) => Poll::Ready(Ok((sender, request))),
            RecvResult::RetryLater(_) => {
                let mut waker = Some(cx.waker().clone());
                let mut guard = SELECTOR.lock();

                match guard.send_command(
                    &this.server.data.node.context,
                    Command::ActionServer {
                        data: this.server.data.clone(),
                        goal: Box::new(move || {
                            let w = waker.take().unwrap();
                            w.wake();
                            CallbackResult::Remove
                        }),
                        cancel: Box::new(move || CallbackResult::Ok),
                        result: Box::new(move || CallbackResult::Ok),
                    },
                ) {
                    Ok(_) => {
                        *this.is_waiting = true;
                        Poll::Pending
                    }
                    Err(e) => Poll::Ready(Err(e)),
                }
            }
            RecvResult::Err(e) => Poll::Ready(Err(e)),
        }
    }
}

#[pinned_drop]
impl<T: ActionMsg> PinnedDrop for AsyncGoalReceiver<T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.server.data.node.context,
                Command::RemoveActionServer(self.server.data.clone()),
            );
        }
    }
}

pub struct ServerCancelSend<T: ActionMsg> {
    data: Arc<ServerData>,
    results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,
    handles: Arc<Mutex<BTreeMap<[u8; 16], *mut rcl_action_goal_handle_t>>>,

    request_id: rmw_request_id_t,
    _unsync: PhantomUnsync,
}

impl<T: ActionMsg> ServerCancelSend<T> {
    /// Accept the cancel requests for accepted_goals and set them to CANCELING state. The shutdown operation should be performed after calling accept(), and you should call send() when it's done.
    pub fn accept(&self, accepted_goals: &Vec<GoalInfo>) -> Result<(), DynError> {
        let server = unsafe { self.data.as_ptr_mut() };

        let accepted_uuids: Vec<[u8; 16]> = accepted_goals
            .iter()
            .map(|goal| goal.goal_id.uuid)
            .collect();

        let handles = self.handles.lock();
        for uuid in accepted_uuids {
            let handle = handles.get(&uuid).unwrap();
            update_goal_state(*handle, GoalEvent::CancelGoal)?;
        }

        Ok(())
    }

    /// Send a response for CancelGoal service.
    pub fn send(
        mut self,
        mut accepted_goals: Vec<GoalInfo>,
    ) -> Result<Server<T>, (Self, DynError)> {
        let mut response = rcl::MTSafeFn::rcl_action_get_zero_initialized_cancel_response();

        response.msg.return_code = if accepted_goals.is_empty() {
            ERROR_REJECTED
        } else {
            ERROR_NONE
        };
        response.msg.goals_canceling = action_msgs__msg__GoalInfo__Sequence {
            data: accepted_goals.as_mut_ptr() as *mut _ as *mut action_msgs__msg__GoalInfo,
            size: accepted_goals.len() as rcl::size_t,
            capacity: accepted_goals.capacity() as rcl::size_t,
        };

        let server = unsafe { self.data.as_ptr_mut() };

        let guard = rcl::MT_UNSAFE_FN.lock();
        match guard.rcl_action_send_cancel_response(
            server,
            &mut self.request_id,
            &mut response.msg as *const _ as *mut _,
        ) {
            Ok(()) => Ok(Server {
                data: self.data,
                results: self.results,
                handles: self.handles,
            }),
            Err(e) => Err((self, e.into())),
        }
    }
}

#[pin_project(PinnedDrop)]
#[must_use]
pub struct AsyncCancelReceiver<T: ActionMsg> {
    server: Server<T>,
    is_waiting: bool,
}

impl<T: ActionMsg> Future for AsyncCancelReceiver<T> {
    type Output = Result<(ServerCancelSend<T>, Vec<GoalInfo>), DynError>;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();
        *this.is_waiting = false;

        match this.server.try_recv_cancel_request() {
            RecvResult::Ok((sender, _req, goals)) => Poll::Ready(Ok((sender, goals))),
            RecvResult::RetryLater(_) => {
                let mut waker = Some(cx.waker().clone());
                let mut guard = SELECTOR.lock();

                match guard.send_command(
                    &this.server.data.node.context,
                    Command::ActionServer {
                        data: this.server.data.clone(),
                        goal: Box::new(move || CallbackResult::Ok),
                        cancel: Box::new(move || {
                            let w = waker.take().unwrap();
                            w.wake();
                            CallbackResult::Remove
                        }),
                        result: Box::new(move || CallbackResult::Ok),
                    },
                ) {
                    Ok(_) => {
                        *this.is_waiting = true;
                        Poll::Pending
                    }
                    Err(e) => Poll::Ready(Err(e)),
                }
            }
            RecvResult::Err(e) => Poll::Ready(Err(e)),
        }
    }
}

#[pinned_drop]
impl<T: ActionMsg> PinnedDrop for AsyncCancelReceiver<T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.server.data.node.context,
                Command::RemoveActionServer(self.server.data.clone()),
            );
        }
    }
}

pub struct ServerResultSend<T: ActionMsg> {
    data: Arc<ServerData>,
    results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,

    request_id: rmw_request_id_t,
    _unsync: PhantomUnsync,
}

impl<T: ActionMsg> ServerResultSend<T> {
    pub fn send(mut self, uuid: &[u8; 16]) -> Result<Server<T>, (Self, DynError)> {
        let removed = {
            let mut results = self.results.lock();
            results.remove(uuid)
        };
        match removed {
            Some(result) => {
                let mut response = T::new_result_response(GoalStatus::Succeeded as u8, result);
                let guard = rcl::MT_UNSAFE_FN.lock();
                match guard.rcl_action_send_result_response(
                    unsafe { self.data.as_ptr_mut() },
                    &mut self.request_id,
                    &mut response as *const _ as *mut _,
                ) {
                    Ok(()) => {
                        return Ok(Server {
                            data: self.data,
                            results: self.results,
                            // TODO: we don't need handles anymore
                            handles: Arc::new(Mutex::new(BTreeMap::new())),
                        });
                    }
                    Err(e) => {
                        let logger = Logger::new("safe_drive");
                        pr_error_in!(
                            logger,
                            "failed to send result response from action server: {}",
                            e
                        );
                        return Err((self, e.into()));
                    }
                }
            }
            None => {
                let logger = Logger::new("safe_drive");
                pr_error_in!(
                    logger,
                    "The result for the goal (uuid: {:?}) is not available yet",
                    uuid
                );
                let e = format!(
                    "The result for the goal (uuid: {:?}) is not available yet",
                    uuid
                );

                return Err((self, e.into()));
            }
        }
    }
}

#[pin_project(PinnedDrop)]
#[must_use]
pub struct AsyncResultReceiver<T: ActionMsg> {
    server: Server<T>,
    is_waiting: bool,
}

impl<T: ActionMsg> Future for AsyncResultReceiver<T> {
    type Output = Result<(ServerResultSend<T>, GetResultServiceRequest<T>), DynError>;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();
        *this.is_waiting = false;

        match this.server.try_recv_result_request() {
            RecvResult::Ok(result) => Poll::Ready(Ok(result)),
            RecvResult::RetryLater(_) => {
                let mut waker = Some(cx.waker().clone());
                let mut guard = SELECTOR.lock();

                match guard.send_command(
                    &this.server.data.node.context,
                    Command::ActionServer {
                        data: this.server.data.clone(),
                        goal: Box::new(move || CallbackResult::Ok),
                        cancel: Box::new(move || CallbackResult::Ok),
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
            RecvResult::Err(e) => Poll::Ready(Err(e)),
        }
    }
}

#[pinned_drop]
impl<T: ActionMsg> PinnedDrop for AsyncResultReceiver<T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.server.data.node.context,
                Command::RemoveActionServer(self.server.data.clone()),
            );
        }
    }
}

impl<T: ActionMsg> Clone for Server<T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            results: self.results.clone(),
            handles: self.handles.clone(),
        }
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

fn get_timestamp(clock: &mut Clock) -> UnsafeTime {
    let now_nanosec = clock.get_now().unwrap();
    let now_sec = now_nanosec / 10_i64.pow(9);
    UnsafeTime {
        sec: now_sec as i32,
        nanosec: (now_nanosec - now_sec * 10_i64.pow(9)) as u32,
    }
}
