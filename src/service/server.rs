use super::Header;
use crate::{
    error::{DynError, RCLError, RCLResult},
    node::Node,
    qos::Profile,
    rcl::{self, rmw_request_id_t},
    selector::async_selector::{self, SELECTOR},
    PhantomUnsync,
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

pub struct Server<T1, T2> {
    pub(crate) data: Arc<ServerData>,
    _phantom: PhantomData<(T1, T2)>,
    _unsync: PhantomUnsync,
}

impl<T1, T2> Server<T1, T2> {
    pub(crate) fn new(
        node: Arc<Node>,
        service_name: &str,
        type_support: *const (),
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
                type_support as _,
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
    /// this returns `Err(RCLError::ServiceTakeFailed)` if there is no available data.
    /// So, please retry later if this error is returned.
    ///
    /// # Return value
    ///
    /// `Ok((ServerSend<T1, T2>, T1))` is returned.
    /// `T1` is a type of request.
    /// After receiving a request, `ServerSend` can be used to send a response.
    ///
    /// # Errors
    ///
    /// `Err((self, RCLError))` is returned when error.
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::ServiceTakeFailed` if take failed but no error occurred in the middleware, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn try_recv(self) -> RCLResult<(ServerSend<T1, T2>, T1)> {
        let (s, d, _) = self.try_recv_with_header()?;
        Ok((s, d))
    }

    /// `try_recv_with_header` equivalent to `try_recv`, but
    /// this function returns `super::Header` including some information together.
    /// `Err(RCLError::ServiceTakeFailed)` is returned if there is no available data.
    /// So, please retry later if this error is returned.
    ///
    /// # Return value
    ///
    /// `Ok((ServerSend<T1, T2>, T1, Header))` is returned.
    /// `T1` is a type of request.
    /// After receiving a request, `ServerSend` can be used to send a response.
    ///
    /// # Errors
    ///
    /// `Err((self, RCLError))` is returned when error.
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::ServiceTakeFailed` if take failed but no error occurred in the middleware, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn try_recv_with_header(self) -> RCLResult<(ServerSend<T1, T2>, T1, Header)> {
        let (request, header) = match rcl_take_request_with_info::<T1>(&self.data.service) {
            Ok(data) => data,
            Err(e) => return Err(e),
        };

        Ok((
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
    /// `Ok((ServerSend<T1, T2>, T1, Header))` is returned.
    /// `T1` is a type of request.
    /// After receiving a request, `ServerSend` can be used to send a response.
    ///
    /// # Errors
    ///
    /// `Err((self, RCLError))` is returned when error.
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub async fn recv_with_header(self) -> Result<(ServerSend<T1, T2>, T1, Header), DynError> {
        AsyncReceiver {
            server: self,
            is_waiting: false,
            _phantom: Default::default(),
        }
        .await
    }

    /// Receive a request asynchronously.
    ///
    /// # Return value
    ///
    /// `Ok((ServerSend<T1, T2>, T1))` is returned.
    /// `T1` is a type of request.
    /// After receiving a request, `ServerSend` can be used to send a response.
    ///
    /// # Errors
    ///
    /// `Err((self, RCLError))` is returned when error.
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub async fn recv(self) -> Result<(ServerSend<T1, T2>, T1), DynError> {
        let (srv, val, _) = self.recv_with_header().await?;
        Ok((srv, val))
    }
}

unsafe impl<T1, T2> Send for Server<T1, T2> {}

pub struct ServerSend<T1, T2> {
    data: Arc<ServerData>,
    request_id: rmw_request_id_t,
    _phantom: PhantomData<(T1, T2)>,
    _unsync: PhantomUnsync,
}

impl<T1, T2> ServerSend<T1, T2> {
    /// Send a response to the client.
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::ServiceInvalid` if the service is invalid, or
    /// - `RCLError::Error` if an unspecified error occurs.
    ///
    /// # Notes
    ///
    /// `data` should be immutable, but `rcl_send_response` provided
    /// by ROS2 takes normal pointers instead of `const` pointers.
    /// So, currently, `send` takes `data` as mutable.
    pub fn send(mut self, mut data: T2) -> RCLResult<Server<T1, T2>> {
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

pub struct AsyncReceiver<T1, T2> {
    server: Server<T1, T2>,
    is_waiting: bool,
    _phantom: PhantomData<(T1, T2)>,
}

impl<T1, T2> Future for AsyncReceiver<T1, T2> {
    type Output = Result<(ServerSend<T1, T2>, T1, Header), DynError>;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        let (server, is_waiting) = unsafe {
            let this = self.get_unchecked_mut();
            (&this.server, &mut this.is_waiting)
        };
        *is_waiting = false;

        match rcl_take_request_with_info::<T1>(&server.data.service) {
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
                        Box::new(move || waker.clone().wake()),
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

impl<T1, T2> Drop for AsyncReceiver<T1, T2> {
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
