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
//! selector.add_wall_timer(Duration::from_millis(100), Box::new(|| ()));
//!
//! // Add a callback of the server.
//! selector.add_server(
//!     server,
//!     Box::new(|request, header| {
//!         // Create a response.
//!         let response = std_srvs::srv::EmptyResponse::new().unwrap();
//!         response
//!     }),
//!     false,
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
//!     context::Context, logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_warn,
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
//!     let dur = Duration::from_millis(200);
//!
//!     loop {
//!         // Call recv() by using timeout.
//!         if let Ok(result) = async_std::future::timeout(dur, server.recv()).await {
//!             match result {
//!                 Ok((sender, request)) => {
//!                     let response = std_srvs::srv::EmptyResponse::new().unwrap();
//!                     let s = sender.send(response).unwrap();
//!                     server = s; // Get a new server to handle next request.
//!                 }
//!                 Err(e) => {
//!                     pr_error!(logger, "error: {e}");
//!                     return;
//!                 }
//!             }
//!         } else {
//!             pr_warn!(logger, "timeout");
//!             return;
//!         }
//!     }
//! }
//!
//! async_std::task::block_on(server_task(server, logger)); // Spawn an asynchronous task.
//! ```

use super::Header;
use crate::{
    error::{DynError, RCLError, RCLResult},
    is_halt,
    msg::ServiceMsg,
    node::Node,
    qos::Profile,
    rcl::{self, rmw_request_id_t},
    selector::{
        async_selector::{self, SELECTOR},
        CallbackResult,
    },
    PhantomUnsync, RecvResult,
};
use std::{
    ffi::CString, future::Future, marker::PhantomData, mem::MaybeUninit, os::raw::c_void,
    sync::Arc, task::Poll,
};

pub(crate) struct ServerData {
    pub(crate) service: rcl::rcl_service_t,
    pub(crate) node: Arc<Node>,
}

impl Drop for ServerData {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard
            .rcl_service_fini(&mut self.service, unsafe { self.node.as_ptr_mut() })
            .unwrap();
    }
}

unsafe impl Sync for ServerData {}
unsafe impl Send for ServerData {}

/// Server.
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
            allocator: rcl::MTSafeFn::rcutils_get_default_allocator(),
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
    /// this returns `RecvResult::RetryLater` if there is no available data.
    /// So, please retry later if this error is returned.
    ///
    /// # Return value
    ///
    /// `RecvResult::Ok((ServerSend<T1, T2>, T1))` is returned.
    /// `T1` is a type of request.
    /// After receiving a request, `ServerSend` can be used to send a response.
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
    ///             RecvResult::Ok((sender, request)) => {
    ///                 let msg = std_srvs::srv::EmptyResponse::new().unwrap();
    ///                 server = sender.send(msg).unwrap();
    ///             }
    ///             RecvResult::RetryLater => {
    ///                 pr_info!(logger, "retry later");
    ///                 break;
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
    pub fn try_recv(self) -> RecvResult<(ServerSend<T>, <T as ServiceMsg>::Request)> {
        let (request, header) =
            match rcl_take_request_with_info::<<T as ServiceMsg>::Request>(&self.data.service) {
                Ok(data) => data,
                Err(RCLError::ServiceTakeFailed) => return RecvResult::RetryLater,
                Err(e) => return RecvResult::Err(e),
            };

        RecvResult::Ok((
            ServerSend {
                data: self.data,
                request_id: header.request_id,
                _phantom: Default::default(),
                _unsync: Default::default(),
            },
            request,
        ))
    }

    /// `try_recv_with_header` is equivalent to `try_recv`, but
    /// this function returns `super::Header` including some information together.
    /// `RecvResult::RetryLater` is returned if there is no available data.
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
    ///         match server.try_recv_with_header() {
    ///             RecvResult::Ok((sender, request, header)) => {
    ///                 pr_info!(logger, "received: header = {:?}", header);
    ///                 let msg = std_srvs::srv::EmptyResponse::new().unwrap();
    ///                 server = sender.send(msg).unwrap();
    ///             }
    ///             RecvResult::RetryLater => {
    ///                 pr_info!(logger, "retry later");
    ///                 break;
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
    pub fn try_recv_with_header(
        self,
    ) -> RecvResult<(ServerSend<T>, <T as ServiceMsg>::Request, Header)> {
        let (request, header) =
            match rcl_take_request_with_info::<<T as ServiceMsg>::Request>(&self.data.service) {
                Ok(data) => data,
                Err(RCLError::ServiceTakeFailed) => return RecvResult::RetryLater,
                Err(e) => return RecvResult::Err(e),
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
    /// This function returns `super::Header` including some information together.
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
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_info, pr_warn,
    ///     service::server::Server,
    /// };
    /// use std::time::Duration;
    ///
    /// async fn server_task(mut server: Server<std_srvs::srv::Empty>, logger: Logger) {
    ///     let dur = Duration::from_millis(200);
    ///
    ///     loop {
    ///         // Call recv_with_header() by using timeout.
    ///         if let Ok(result) = async_std::future::timeout(dur, server.recv_with_header()).await {
    ///             match result {
    ///                 Ok((sender, request, header)) => {
    ///                     pr_info!(logger, "recv: header = {:?}", header);
    ///                     let response = std_srvs::srv::EmptyResponse::new().unwrap();
    ///                     let s = sender.send(response).unwrap();
    ///                     server = s; // Get a new server to handle next request.
    ///                 }
    ///                 Err(e) => {
    ///                     pr_error!(logger, "error: {e}");
    ///                     return;
    ///                 }
    ///             }
    ///         } else {
    ///             pr_warn!(logger, "timeout");
    ///             return;
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
    pub async fn recv_with_header(
        self,
    ) -> Result<(ServerSend<T>, <T as ServiceMsg>::Request, Header), DynError> {
        AsyncReceiver {
            server: self,
            is_waiting: false,
        }
        .await
    }

    /// Receive a request asynchronously.
    ///
    /// # Return value
    ///
    /// `Ok((ServerSend<T>, <T as ServiceMsg>::Request)` is returned.
    /// `T` is a type of the request and response.
    /// After receiving a request, `ServerSend<T>` can be used to send a response.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_warn, service::server::Server,
    /// };
    /// use std::time::Duration;
    ///
    /// async fn server_task(mut server: Server<std_srvs::srv::Empty>, logger: Logger) {
    ///     let dur = Duration::from_millis(200);
    ///
    ///     loop {
    ///         // Call recv() by using timeout.
    ///         if let Ok(result) = async_std::future::timeout(dur, server.recv()).await {
    ///             match result {
    ///                 Ok((sender, request)) => {
    ///                     let response = std_srvs::srv::EmptyResponse::new().unwrap();
    ///                     let s = sender.send(response).unwrap();
    ///                     server = s; // Get a new server to handle next request.
    ///                 }
    ///                 Err(e) => {
    ///                     pr_error!(logger, "error: {e}");
    ///                     return;
    ///                 }
    ///             }
    ///         } else {
    ///             pr_warn!(logger, "timeout");
    ///             return;
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// `Err((self, RCLError))` is returned when error.
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub async fn recv(self) -> Result<(ServerSend<T>, <T as ServiceMsg>::Request), DynError> {
        let (srv, val, _) = self.recv_with_header().await?;
        Ok((srv, val))
    }
}

unsafe impl<T> Send for Server<T> {}

/// Sender to send a response.
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
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_warn, service::server::Server,
    /// };
    /// use std::time::Duration;
    ///
    /// async fn server_task(mut server: Server<std_srvs::srv::Empty>, logger: Logger) {
    ///     let dur = Duration::from_millis(200);
    ///
    ///     loop {
    ///         // Call recv() by using timeout.
    ///         if let Ok(result) = async_std::future::timeout(dur, server.recv()).await {
    ///             match result {
    ///                 Ok((sender, request)) => {
    ///                     let response = std_srvs::srv::EmptyResponse::new().unwrap();
    ///                     let s = sender.send(response).unwrap();
    ///                     server = s; // Get a new server to handle next request.
    ///                 }
    ///                 Err(e) => {
    ///                     pr_error!(logger, "error: {e}");
    ///                     return;
    ///                 }
    ///             }
    ///         } else {
    ///             pr_warn!(logger, "timeout");
    ///             return;
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
    pub fn send(mut self, mut data: <T as ServiceMsg>::Response) -> RCLResult<Server<T>> {
        if let Err(e) = rcl::MTSafeFn::rcl_send_response(
            &self.data.service,
            &mut self.request_id,
            &mut data as *mut _ as *mut c_void,
        ) {
            return Err(e);
        }

        Ok(Server {
            data: self.data,
            _phantom: Default::default(),
            _unsync: Default::default(),
        })
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
            return Poll::Ready(Err("Signaled".into()));
        }

        let (server, is_waiting) = unsafe {
            let this = self.get_unchecked_mut();
            (&this.server, &mut this.is_waiting)
        };
        *is_waiting = false;

        match rcl_take_request_with_info::<<T as ServiceMsg>::Request>(&server.data.service) {
            Ok((request, header)) => Poll::Ready(Ok((
                ServerSend {
                    data: server.data.clone(),
                    request_id: header.request_id,
                    _phantom: Default::default(),
                    _unsync: Default::default(),
                },
                request,
                Header { header },
            ))),
            Err(RCLError::ServiceTakeFailed) => {
                let waker = cx.waker().clone();
                let mut guard = SELECTOR.lock();
                if let Err(e) = guard.send_command(
                    &server.data.node.context,
                    async_selector::Command::Server(
                        server.data.clone(),
                        Box::new(move || {
                            waker.clone().wake();
                            CallbackResult::Ok
                        }),
                    ),
                ) {
                    return Poll::Ready(Err(e));
                }

                *is_waiting = true;
                Poll::Pending
            }
            Err(e) => Poll::Ready(Err(e.into())),
        }
    }
}

impl<T> Drop for AsyncReceiver<T> {
    fn drop(&mut self) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            guard
                .send_command(
                    &self.server.data.node.context,
                    async_selector::Command::RemoveServer(self.server.data.clone()),
                )
                .unwrap();
        }
    }
}
