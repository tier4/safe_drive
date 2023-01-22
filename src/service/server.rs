//! Server to receive a request and send the reply.
//!
//! # Examples
//!
//! ## Single Threaded Execution
//!
//! ```
//! use safe_drive::{context::Context, msg::common_interfaces::std_srvs};
//! use std::time::Duration;
//!
//! // Create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create a server node.
//! let node = ctx
//!     .create_node("service_server_rs", None, Default::default())
//!     .unwrap();
//!
//! // Create a server.
//! let server = node
//!     .create_server::<std_srvs::srv::Empty>("service_name1", None)
//!     .unwrap();
//!
//! // Create a selector.
//! let mut selector = ctx.create_selector().unwrap();
//!
//! // Add a wall timer.
//! selector.add_wall_timer("timer_name", Duration::from_millis(100), Box::new(|| ()));
//!
//! // Add a callback of the server.
//! selector.add_server(
//!     server,
//!     Box::new(|request, header| {
//!         // Create a response.
//!         let response = std_srvs::srv::EmptyResponse::new().unwrap();
//!         response
//!     })
//! );
//!
//! for _ in 0..2 {
//!     selector.wait().unwrap();
//! }
//! ```
//!
//! ## Multi Threaded Execution
//!
//! ```
//! use safe_drive::{
//!     context::Context, logger::Logger, msg::common_interfaces::std_srvs, pr_error,
//!     service::server::Server,
//! };
//! use std::time::Duration;
//!
//! // Create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create a server node.
//! let node = ctx.create_node("service_server_rs", None, Default::default()).unwrap();
//!
//! // Create a server.
//! let server = node
//!     .create_server::<std_srvs::srv::Empty>("service_name1", None)
//!     .unwrap();
//!
//! let logger = Logger::new("service_rs");
//!
//! async fn server_task(mut server: Server<std_srvs::srv::Empty>, logger: Logger) {
//!     loop {
//!         // Receive a request.
//!         let req = server.recv().await;
//!         match req {
//!             Ok((sender, request, _header)) => {
//!                 let response = std_srvs::srv::EmptyResponse::new().unwrap();
//!                 match sender.send(&response) {
//!                     Ok(s) => server = s,                  // Get a new server to handle next request.
//!                     Err((s, _e)) => server = s.give_up(), // Failed to send.
//!                 }
//!             }
//!             Err(e) => {
//!                 pr_error!(logger, "error: {e}");
//!                 return;
//!             }
//!         }
//!     }
//! }
//!
//! // We don't call `server_task` here because testing this code will block forever.
//! // async_std::task::block_on(server_task(server, logger)); // Spawn an asynchronous task.
//! ```

use super::Header;
use crate::{
    error::{DynError, RCLError, RCLResult},
    get_allocator, is_halt,
    msg::ServiceMsg,
    node::Node,
    qos::Profile,
    rcl::{self, rmw_request_id_t},
    selector::{
        async_selector::{self, SELECTOR},
        CallbackResult,
    },
    signal_handler::Signaled,
    PhantomUnsync, RecvResult,
};
use pin_project::{pin_project, pinned_drop};
use std::{
    ffi::CString, future::Future, marker::PhantomData, mem::MaybeUninit, os::raw::c_void, pin::Pin,
    sync::Arc, task::Poll,
};

pub(crate) struct ServerData {
    pub(crate) service: rcl::rcl_service_t,
    pub(crate) node: Arc<Node>,
}

impl Drop for ServerData {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_service_fini(&mut self.service, unsafe { self.node.as_ptr_mut() });
    }
}

unsafe impl Sync for ServerData {}
unsafe impl Send for ServerData {}

/// Server.
#[must_use]
pub struct Server<T> {
    pub(crate) data: Arc<ServerData>,
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T: ServiceMsg> Server<T> {
    pub(crate) fn new(
        node: Arc<Node>,
        service_name: &str,
        qos: Option<Profile>,
    ) -> RCLResult<Self> {
        let mut service = rcl::MTSafeFn::rcl_get_zero_initialized_service();
        let service_name = CString::new(service_name).unwrap_or_default();
        let profile = qos.unwrap_or_else(Profile::services_default);
        let options = rcl::rcl_service_options_t {
            qos: (&profile).into(),
            allocator: get_allocator(),
        };

        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_service_init(
                &mut service,
                node.as_ptr(),
                <T as ServiceMsg>::type_support(),
                service_name.as_ptr(),
                &options,
            )?;
        }

        Ok(Server {
            data: Arc::new(ServerData { service, node }),
            _phantom: Default::default(),
            _unsync: Default::default(),
        })
    }

    /// Receive a request.
    /// `try_recv` is a non-blocking function, and
    /// this returns `RecvResult::RetryLater(self)` if there is no available data.
    /// So, please retry later if this error is returned.
    ///
    /// # Return value
    ///
    /// `RecvResult::Ok((ServerSend<T>, <T as ServiceMsg>::Request, Header))` is returned.
    /// `T` is a type of the request and response.
    /// After receiving a request, `ServerSend<T>` can be used to send a response.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_info, service::server::Server,
    ///     RecvResult,
    /// };
    ///
    /// fn server_fn(mut server: Server<std_srvs::srv::Empty>, logger: Logger) {
    ///     loop {
    ///         match server.try_recv() {
    ///             RecvResult::Ok((sender, request, header)) => {
    ///                 pr_info!(logger, "received: header = {:?}", header);
    ///                 let msg = std_srvs::srv::EmptyResponse::new().unwrap();
    ///                 match sender.send(&msg) {
    ///                     Ok(s) => server = s,                  // Get a new server to handle next request.
    ///                     Err((s, _e)) => server = s.give_up(), // Failed to send.
    ///                 }
    ///             }
    ///             RecvResult::RetryLater(s) => {
    ///                 pr_info!(logger, "retry later");
    ///                 server = s;
    ///             }
    ///             RecvResult::Err(e) => {
    ///                 pr_error!(logger, "error: {e}");
    ///                 break;
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::Error` if an unspecified error occurs.
    #[must_use]
    pub fn try_recv(self) -> RecvResult<(ServerSend<T>, <T as ServiceMsg>::Request, Header), Self> {
        let (request, header) =
            match rcl_take_request_with_info::<<T as ServiceMsg>::Request>(&self.data.service) {
                Ok(data) => data,
                Err(RCLError::ServiceTakeFailed) => return RecvResult::RetryLater(self),
                Err(e) => return RecvResult::Err(e.into()),
            };

        RecvResult::Ok((
            ServerSend {
                data: self.data,
                request_id: header.request_id,
                _phantom: Default::default(),
                _unsync: Default::default(),
            },
            request,
            Header { header },
        ))
    }

    /// Receive a request asynchronously.
    ///
    /// # Return value
    ///
    /// `Ok((ServerSend<T>, <T as ServiceMsg>::Request, T1, Header))` is returned.
    /// `T` is a type of the request and response.
    /// After receiving a request, `ServerSend<T>` can be used to send a response.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_info, service::server::Server,
    /// };
    ///
    /// async fn server_task(mut server: Server<std_srvs::srv::Empty>, logger: Logger) {
    ///     loop {
    ///         // Receive a request.
    ///         let req = server.recv().await;
    ///         match req {
    ///             Ok((sender, request, header)) => {
    ///                 pr_info!(logger, "recv: header = {:?}", header);
    ///                 let response = std_srvs::srv::EmptyResponse::new().unwrap();
    ///                 match sender.send(&response) {
    ///                     Ok(s) => server = s,                  // Get a new server to handle next request.
    ///                     Err((s, _e)) => server = s.give_up(), // Failed to send.
    ///                 }
    ///             }
    ///             Err(e) => {
    ///                 pr_error!(logger, "error: {e}");
    ///                 return;
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub async fn recv(
        self,
    ) -> Result<(ServerSend<T>, <T as ServiceMsg>::Request, Header), DynError> {
        AsyncReceiver {
            server: self,
            is_waiting: false,
        }
        .await
    }
}

unsafe impl<T> Send for Server<T> {}

/// Sender to send a response.
#[must_use]
pub struct ServerSend<T> {
    data: Arc<ServerData>,
    request_id: rmw_request_id_t,
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T: ServiceMsg> ServerSend<T> {
    /// Send a response to the client.
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::Error` if an unspecified error occurs.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, service::server::Server,
    /// };
    ///
    /// async fn server_task(mut server: Server<std_srvs::srv::Empty>, logger: Logger) {
    ///     loop {
    ///         // Call recv() by using timeout.
    ///         let req = server.recv().await;
    ///         match req {
    ///             Ok((sender, request, _header)) => {
    ///                 let response = std_srvs::srv::EmptyResponse::new().unwrap();
    ///                 match sender.send(&response) {
    ///                     Ok(s) => server = s,                  // Get a new server to handle next request.
    ///                     Err((s, _e)) => server = s.give_up(), // Failed to send.
    ///                 }
    ///             }
    ///             Err(e) => {
    ///                 pr_error!(logger, "error: {e}");
    ///                 return;
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// # Notes
    ///
    /// `data` should be immutable, but `rcl_send_response` provided
    /// by ROS2 takes normal pointers instead of `const` pointers.
    /// So, currently, `send` takes `data` as mutable.
    pub fn send(
        mut self,
        data: &<T as ServiceMsg>::Response,
    ) -> Result<Server<T>, (Self, RCLError)> {
        if let Err(e) = rcl::MTSafeFn::rcl_send_response(
            &self.data.service,
            &mut self.request_id,
            data as *const _ as *mut c_void,
        ) {
            return Err((self, e));
        }

        Ok(Server {
            data: self.data,
            _phantom: Default::default(),
            _unsync: Default::default(),
        })
    }

    pub fn give_up(self) -> Server<T> {
        Server {
            data: self.data,
            _phantom: Default::default(),
            _unsync: Default::default(),
        }
    }
}

fn rcl_take_request_with_info<T>(
    service: &rcl::rcl_service_t,
) -> RCLResult<(T, rcl::rmw_service_info_t)> {
    let mut header: rcl::rmw_service_info_t = unsafe { MaybeUninit::zeroed().assume_init() };
    let mut ros_request: T = unsafe { MaybeUninit::zeroed().assume_init() };

    let guard = rcl::MT_UNSAFE_FN.lock();
    guard.rcl_take_request_with_info(
        service,
        &mut header,
        &mut ros_request as *mut _ as *mut c_void,
    )?;

    Ok((ros_request, header))
}

/// Receiver to receive a request asynchronously.
#[pin_project(PinnedDrop)]
#[must_use]
pub struct AsyncReceiver<T> {
    server: Server<T>,
    is_waiting: bool,
}

impl<T: ServiceMsg> Future for AsyncReceiver<T> {
    type Output = Result<(ServerSend<T>, <T as ServiceMsg>::Request, Header), DynError>;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();

        // let (server, is_waiting) = unsafe {
        //     let this = self.get_unchecked_mut();
        //     (&this.server, &mut this.is_waiting)
        // };
        *this.is_waiting = false;

        match rcl_take_request_with_info::<<T as ServiceMsg>::Request>(&this.server.data.service) {
            Ok((request, header)) => Poll::Ready(Ok((
                ServerSend {
                    data: this.server.data.clone(),
                    request_id: header.request_id,
                    _phantom: Default::default(),
                    _unsync: Default::default(),
                },
                request,
                Header { header },
            ))),
            Err(RCLError::ServiceTakeFailed) => {
                let mut waker = Some(cx.waker().clone());
                let mut guard = SELECTOR.lock();
                if let Err(e) = guard.send_command(
                    &this.server.data.node.context,
                    async_selector::Command::Server(
                        this.server.data.clone(),
                        Box::new(move || {
                            let w = waker.take().unwrap();
                            w.wake();
                            CallbackResult::Ok
                        }),
                    ),
                ) {
                    return Poll::Ready(Err(e));
                }

                *this.is_waiting = true;
                Poll::Pending
            }
            Err(e) => Poll::Ready(Err(e.into())),
        }
    }
}

#[pinned_drop]
impl<T> PinnedDrop for AsyncReceiver<T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.server.data.node.context,
                async_selector::Command::RemoveServer(self.server.data.clone()),
            );
        }
    }
}
