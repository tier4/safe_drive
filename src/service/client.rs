//! Client to send a request and receive the reply.
//!
//! The callback execution is not suitable for request and response based communications.
//! So, use async/await to use `Client`.
//!
//! # Example
//!
//! ```
//! use safe_drive::{
//!     context::Context, logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_info,
//!     pr_warn, service::client::Client,
//! };
//! use std::time::Duration;
//!
//! // Create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create a server node.
//! let node = ctx
//!     .create_node("service_client_rs", None, Default::default())
//!     .unwrap();
//!
//! // Create a client.
//! let client = node
//!     .create_client::<std_srvs::srv::Empty>("service_name1", None)
//!     .unwrap();
//!
//! // Create a logger.
//! let logger = Logger::new("client_rs");
//!
//! async fn run_client(mut client: Client<std_srvs::srv::Empty>, logger: Logger) {
//!     let dur = Duration::from_millis(100);
//!
//!     for _ in 0..5 {
//!         let request = std_srvs::srv::EmptyRequest::new().unwrap();
//!         let mut receiver = client.send(&request).unwrap().recv();
//!         match async_std::future::timeout(dur, &mut receiver).await {
//!             Ok(Ok((c, response, _header))) => {
//!                 pr_info!(logger, "received: {:?}", response);
//!                 client = c;
//!             }
//!             Ok(Err(e)) => {
//!                 pr_error!(logger, "error: {e}");
//!                 break;
//!             }
//!             Err(_) => {
//!                 pr_warn!(logger, "timeout");
//!                 client = receiver.give_up();
//!             }
//!         }
//!     }
//! }
//!
//! async_std::task::block_on(run_client(client, logger)); // Spawn an asynchronous task.
//! ```

use super::Header;
use crate::{
    error::{DynError, RCLError, RCLResult},
    is_halt,
    msg::ServiceMsg,
    node::Node,
    qos::Profile,
    rcl,
    selector::{
        async_selector::{self, SELECTOR},
        CallbackResult,
    },
    signal_handler::Signaled,
    PhantomUnsync, RecvResult,
};
use std::{
    ffi::CString, future::Future, marker::PhantomData, mem::MaybeUninit, os::raw::c_void,
    sync::Arc, task::Poll,
};

pub(crate) struct ClientData {
    pub(crate) client: rcl::rcl_client_t,
    pub(crate) node: Arc<Node>,
}

impl Drop for ClientData {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard
            .rcl_client_fini(&mut self.client, unsafe { self.node.as_ptr_mut() })
            .unwrap();
    }
}

unsafe impl Sync for ClientData {}
unsafe impl Send for ClientData {}

/// Client.
pub struct Client<T> {
    data: Arc<ClientData>,
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T: ServiceMsg> Client<T> {
    pub(crate) fn new(
        node: Arc<Node>,
        service_name: &str,
        qos: Option<Profile>,
    ) -> RCLResult<Self> {
        let mut client = rcl::MTSafeFn::rcl_get_zero_initialized_client();
        let service_name = CString::new(service_name).unwrap_or_default();
        let profile = qos.unwrap_or_else(Profile::services_default);
        let options = rcl::rcl_client_options_t {
            qos: (&profile).into(),
            allocator: rcl::MTSafeFn::rcutils_get_default_allocator(),
        };

        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_client_init(
            &mut client,
            node.as_ptr(),
            <T as ServiceMsg>::type_support(),
            service_name.as_ptr(),
            &options,
        )?;

        Ok(Client {
            data: Arc::new(ClientData { client, node }),
            _phantom: Default::default(),
            _unsync: Default::default(),
        })
    }

    /// Send a request.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_info, pr_warn, service::client::Client,
    /// };
    /// use std::time::Duration;
    ///
    /// async fn run_client(mut client: Client<std_srvs::srv::Empty>, logger: Logger) {
    ///     let dur = Duration::from_millis(100);
    ///
    ///     loop {
    ///         let request = std_srvs::srv::EmptyRequest::new().unwrap();
    ///         let mut receiver = client.send(&request).unwrap().recv();
    ///         match async_std::future::timeout(dur, &mut receiver).await {
    ///             Ok(Ok((c, response, _header))) => {
    ///                 pr_info!(logger, "received: {:?}", response);
    ///                 client = c;
    ///             }
    ///             Ok(Err(e)) => {
    ///                 pr_error!(logger, "error: {e}");
    ///                 break;
    ///             }
    ///             Err(_) => {
    ///                 pr_warn!(logger, "timeout");
    ///                 client = receiver.give_up();
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ClientInvalid` if the client is invalid, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn send(self, data: &<T as ServiceMsg>::Request) -> RCLResult<ClientRecv<T>> {
        let (s, _) = self.send_ret_seq(data)?;
        Ok(s)
    }

    /// `send_ret_seq` is equivalent to `send`, but this returns
    /// the sequence number together.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_info, pr_warn, service::client::Client,
    /// };
    /// use std::time::Duration;
    ///
    /// async fn run_client(mut client: Client<std_srvs::srv::Empty>, logger: Logger) {
    ///     let dur = Duration::from_millis(100);
    ///
    ///     loop {
    ///         let request = std_srvs::srv::EmptyRequest::new().unwrap();
    ///         let (receiver, sequence) = client.send_ret_seq(&request).unwrap();
    ///         let mut receiver = receiver.recv();
    ///         pr_info!(logger, "sent: sequence = {sequence}");
    ///         match async_std::future::timeout(dur, &mut receiver).await {
    ///             Ok(Ok((c, response, _header))) => {
    ///                 pr_info!(logger, "received: {:?}", response);
    ///                 client = c;
    ///             }
    ///             Ok(Err(e)) => {
    ///                 pr_error!(logger, "error: {e}");
    ///                 break;
    ///             }
    ///             Err(_) => {
    ///                 pr_warn!(logger, "timeout");
    ///                 client = receiver.give_up();
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ClientInvalid` if the client is invalid, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn send_ret_seq(
        self,
        data: &<T as ServiceMsg>::Request,
    ) -> RCLResult<(ClientRecv<T>, i64)> {
        let mut seq: i64 = 0;
        if let Err(e) = rcl::MTSafeFn::rcl_send_request(
            &self.data.client,
            data as *const _ as *const c_void,
            &mut seq,
        ) {
            return Err(e);
        }

        Ok((
            ClientRecv {
                data: self.data,
                seq,
                _phantom: Default::default(),
                _unsync: Default::default(),
            },
            seq,
        ))
    }
}

/// Receiver to receive a response.
#[derive(Clone)]
#[must_use]
pub struct ClientRecv<T> {
    pub(crate) data: Arc<ClientData>,
    seq: i64,
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T: ServiceMsg> ClientRecv<T> {
    /// Receive a message.
    /// `try_recv` is a non-blocking function, and this
    /// returns `RecvResult::RetryLater(self)`.
    /// So, please retry later if this value is returned.
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ClientInvalid` if the client is invalid, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn try_recv(self) -> RecvResult<(Client<T>, <T as ServiceMsg>::Response, Header), Self> {
        let (response, header) = match rcl_take_response_with_info::<<T as ServiceMsg>::Response>(
            &self.data.client,
            self.seq,
        ) {
            Ok(data) => data,
            Err(RCLError::ClientTakeFailed) => return RecvResult::RetryLater(self),
            Err(e) => return RecvResult::Err(e),
        };

        if header.request_id.sequence_number != self.seq {
            return RecvResult::RetryLater(self);
        }

        RecvResult::Ok((
            Client {
                data: self.data,
                _phantom: Default::default(),
                _unsync: Default::default(),
            },
            response,
            Header { header },
        ))
    }

    /// Receive a response asynchronously.
    /// this returns `super::Header` including some information together.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_srvs, pr_error, pr_info, pr_warn, service::client::Client,
    /// };
    /// use std::time::Duration;
    ///
    /// async fn run_client(mut client: Client<std_srvs::srv::Empty>, logger: Logger) {
    ///     let dur = Duration::from_millis(100);
    ///
    ///     loop {
    ///         let request = std_srvs::srv::EmptyRequest::new().unwrap();
    ///         let mut receiver = client.send(&request).unwrap().recv();
    ///         match async_std::future::timeout(dur, &mut receiver).await {
    ///             Ok(Ok((c, response, header))) => {
    ///                 pr_info!(logger, "received: header = {:?}", header);
    ///                 client = c;
    ///             }
    ///             Ok(Err(e)) => {
    ///                 pr_error!(logger, "error: {e}");
    ///                 break;
    ///             }
    ///             Err(_) => {
    ///                 pr_warn!(logger, "timeout");
    ///                 client = receiver.give_up();
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ClientInvalid` if the client is invalid, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn recv(self) -> AsyncReceiver<T> {
        AsyncReceiver {
            client: self,
            is_waiting: false,
        }
    }

    /// Give up to receive a response.
    /// If there is no server, nobody responds requests.
    pub fn give_up(self) -> Client<T> {
        Client {
            data: self.data,
            _phantom: Default::default(),
            _unsync: Default::default(),
        }
    }
}

fn rcl_take_response_with_info<T>(
    client: &rcl::rcl_client_t,
    seq: i64,
) -> RCLResult<(T, rcl::rmw_service_info_t)> {
    let mut header: rcl::rmw_service_info_t = unsafe { MaybeUninit::zeroed().assume_init() };
    let mut ros_response: T = unsafe { MaybeUninit::zeroed().assume_init() };

    header.request_id.sequence_number = seq;

    let guard = rcl::MT_UNSAFE_FN.lock();
    guard.rcl_take_response_with_info(
        client,
        &mut header,
        &mut ros_response as *mut _ as *mut c_void,
    )?;

    Ok((ros_response, header))
}

/// Receiver to receive a response asynchronously.
#[must_use]
pub struct AsyncReceiver<T> {
    client: ClientRecv<T>,
    is_waiting: bool,
}

impl<T: ServiceMsg> AsyncReceiver<T> {
    pub fn give_up(self) -> Client<T> {
        Client {
            data: self.client.data.clone(),
            _phantom: Default::default(),
            _unsync: Default::default(),
        }
    }
}

impl<T: ServiceMsg> Future for AsyncReceiver<T> {
    type Output = Result<(Client<T>, <T as ServiceMsg>::Response, Header), DynError>;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let (client, is_waiting) = unsafe {
            let this = self.get_unchecked_mut();
            (&this.client, &mut this.is_waiting)
        };
        *is_waiting = false;

        match rcl_take_response_with_info(&client.data.client, client.seq) {
            Ok((val, header)) => {
                if header.request_id.sequence_number == client.seq {
                    return Poll::Ready(Ok((
                        Client {
                            data: client.data.clone(),
                            _phantom: Default::default(),
                            _unsync: Default::default(),
                        },
                        val,
                        Header { header },
                    )));
                }
            }
            Err(RCLError::ClientTakeFailed) => (),
            Err(e) => return Poll::Ready(Err(e.into())),
        }

        // wait message arrival
        let mut waker = Some(cx.waker().clone());
        let mut guard = SELECTOR.lock();
        if let Err(e) = guard.send_command(
            &client.data.node.context,
            async_selector::Command::Client(
                client.data.clone(),
                Box::new(move || {
                    let w = waker.take().unwrap();
                    w.wake();
                    CallbackResult::Ok
                }),
            ),
        ) {
            return Poll::Ready(Err(e));
        }

        *is_waiting = true;
        Poll::Pending
    }
}

impl<T> Drop for AsyncReceiver<T> {
    fn drop(&mut self) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            guard
                .send_command(
                    &self.client.data.node.context,
                    async_selector::Command::RemoveClient(self.client.data.clone()),
                )
                .unwrap();
        }
    }
}
