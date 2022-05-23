use super::{Header, SrvResult};
use crate::{error::RCLResult, node::Node, qos::Profile, rcl, PhantomUnsync};
use std::{ffi::CString, marker::PhantomData, mem::MaybeUninit, os::raw::c_void, sync::Arc};

struct ClientData {
    client: rcl::rcl_client_t,
    node: Arc<Node>,
}

impl Drop for ClientData {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
        guard
            .rcl_client_fini(&mut self.client, unsafe { self.node.as_ptr_mut() })
            .unwrap();
    }
}

pub struct Client<T1, T2> {
    data: Arc<ClientData>,
    _phantom: PhantomData<(T1, T2)>,
    _unsync: PhantomUnsync,
}

impl<T1, T2> Client<T1, T2> {
    pub(crate) fn new(
        node: Arc<Node>,
        service_name: &str,
        type_support: *const (),
        qos: Option<Profile>,
    ) -> RCLResult<Self> {
        let mut client = rcl::MTSafeFn::rcl_get_zero_initialized_client();
        let service_name = CString::new(service_name).unwrap_or_default();
        let profile = qos.unwrap_or_else(Profile::service_default);
        let options = rcl::rcl_client_options_t {
            qos: (&profile).into(),
            allocator: rcl::MTSafeFn::rcutils_get_default_allocator(),
        };

        let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
        guard.rcl_client_init(
            &mut client,
            node.as_ptr(),
            type_support as _,
            service_name.as_ptr(),
            &options,
        )?;

        Ok(Client {
            data: Arc::new(ClientData { client, node }),
            _phantom: Default::default(),
            _unsync: Default::default(),
        })
    }

    pub fn send(self, data: T1) -> SrvResult<ClientRecv<T1, T2>, Self> {
        let (s, _) = self.send_with_seq(data)?;
        Ok(s)
    }

    pub fn send_with_seq(self, data: T1) -> SrvResult<(ClientRecv<T1, T2>, i64), Self> {
        let mut seq: i64 = 0;
        if let Err(e) = rcl::MTSafeFn::rcl_send_request(
            &self.data.client,
            &data as *const _ as *const c_void,
            &mut seq,
        ) {
            return Err((self, e));
        }

        Ok((
            ClientRecv {
                data: self.data,
                _phantom: Default::default(),
                _unsync: Default::default(),
            },
            seq,
        ))
    }
}

pub struct ClientRecv<T1, T2> {
    data: Arc<ClientData>,
    _phantom: PhantomData<(T1, T2)>,
    _unsync: PhantomUnsync,
}

impl<T1, T2> ClientRecv<T1, T2> {
    pub fn try_recv(self) -> SrvResult<(Client<T1, T2>, T2), Self> {
        let (s, d, _) = self.try_recv_with_header()?;
        Ok((s, d))
    }

    pub fn try_recv_with_header(self) -> SrvResult<(Client<T1, T2>, T2, Header), Self> {
        let (response, header) = match rcl_take_response_with_info::<T2>(&self.data.client) {
            Ok(data) => data,
            Err(e) => return Err((self, e)),
        };

        Ok((
            Client {
                data: self.data,
                _phantom: Default::default(),
                _unsync: Default::default(),
            },
            response,
            Header { header },
        ))
    }
}

fn rcl_take_response_with_info<T>(
    client: &rcl::rcl_client_t,
) -> RCLResult<(T, rcl::rmw_service_info_t)> {
    let mut header: rcl::rmw_service_info_t = unsafe { MaybeUninit::zeroed().assume_init() };
    let mut ros_response: T = unsafe { MaybeUninit::zeroed().assume_init() };

    let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
    guard.rcl_take_response_with_info(
        client,
        &mut header,
        &mut ros_response as *mut _ as *mut c_void,
    )?;

    Ok((ros_response, header))
}
