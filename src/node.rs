//! Node of ROS2.
//! Nodes can be create by `Context::create_node`.
//!
//! # Example
//!
//! ```
//! use safe_drive::context::Context;
//!
//! // Create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create a node.
//! let node = ctx
//!     .create_node("node_rs", Some("namespace"), Default::default())
//!     .unwrap();
//! ```

use libc::atexit;

use crate::{
    context::{remove_context, Context},
    error::{DynError, RCLResult},
    helper::InitOnce,
    msg::{ServiceMsg, TypeSupport},
    parameter::ParameterServer,
    qos, rcl,
    service::{client::Client, server::Server},
    topic::publisher::Publisher,
    topic::subscriber::Subscriber,
};
use std::{ffi::CString, sync::Arc};

static SET_ATEXIT: InitOnce = InitOnce::new();

/// Node of ROS2.
pub struct Node {
    node: rcl::rcl_node_t,
    init_param_server: InitOnce,
    pub(crate) context: Arc<Context>,
}

impl Node {
    pub(crate) fn new(
        context: Arc<Context>,
        name: &str,
        namespace: Option<&str>,
        options: NodeOptions,
    ) -> RCLResult<Arc<Self>> {
        let mut node = rcl::MTSafeFn::rcl_get_zero_initialized_node();

        let name_c = CString::new(name).unwrap();
        let namespace_c = CString::new(namespace.unwrap_or_default()).unwrap();

        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_node_init(
                &mut node,
                name_c.as_ptr(),
                namespace_c.as_ptr(),
                unsafe { context.as_ptr_mut() },
                options.as_ptr(),
            )?;
        }

        // FastDDS uses atexit(3) to destroy resources when creating a node.
        // Because of functions registed to atexit(3) will be invoked reverse order,
        // remove_context() must be set here.
        SET_ATEXIT.init(|| unsafe { atexit(remove_context) }, 0);

        Ok(Arc::new(Node {
            node,
            init_param_server: InitOnce::new(),
            context,
        }))
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_node_t {
        &self.node
    }

    pub(crate) unsafe fn as_ptr_mut(&self) -> *mut rcl::rcl_node_t {
        &self.node as *const _ as *mut _
    }

    pub fn get_name(&self) -> RCLResult<String> {
        rcl::MTSafeFn::rcl_node_get_name(&self.node)
    }

    pub fn get_fully_qualified_name(&self) -> RCLResult<String> {
        rcl::MTSafeFn::rcl_node_get_fully_qualified_name(&self.node)
    }

    pub fn get_namespace(&self) -> RCLResult<String> {
        rcl::MTSafeFn::rcl_node_get_namespace(&self.node)
    }

    pub fn create_parameter_server(self: &Arc<Self>) -> Result<ParameterServer, DynError> {
        self.init_param_server.init(
            || ParameterServer::new(self.clone()),
            Err("a parameter server has been already created".into()),
        )
    }

    /// Create a publisher.
    /// If `qos` is specified `None`,
    /// the default profile is used.
    ///
    /// `T` is the type of messages the created publisher send.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{msg::common_interfaces::std_msgs, node::Node, topic::publisher::Publisher};
    /// use std::sync::Arc;
    ///
    /// fn create_new_publisher(node: Arc<Node>) -> Publisher<std_msgs::msg::Bool> {
    ///     node.create_publisher("topic_name", None).unwrap()
    /// }
    /// ```
    pub fn create_publisher<T: TypeSupport>(
        self: &Arc<Self>,
        topic_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Publisher<T>> {
        Publisher::new(self.clone(), topic_name, qos)
    }

    /// Create a publisher.
    /// If `qos` is specified `None`,
    /// the default profile is used.
    ///
    /// `T` is the type of messages the created publisher send.
    ///
    /// This function is the same as `create_publisher` but it disables loaned message.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{msg::common_interfaces::std_msgs, node::Node, topic::publisher::Publisher};
    /// use std::sync::Arc;
    ///
    /// fn create_publisher_disable_loaned_message(node: Arc<Node>) -> Publisher<std_msgs::msg::Bool> {
    ///     node.create_publisher_disable_loaned_message("topic_name", None).unwrap()
    /// }
    /// ```
    pub fn create_publisher_disable_loaned_message<T: TypeSupport>(
        self: &Arc<Self>,
        topic_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Publisher<T>> {
        Publisher::new_disable_loaned_message(self.clone(), topic_name, qos)
    }

    /// Create a subscriber.
    /// If `qos` is specified `None`,
    /// the default profile is used.
    ///
    /// `T` is the type of messages the created subscriber receive.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{msg::common_interfaces::std_msgs, node::Node, topic::subscriber::Subscriber};
    /// use std::sync::Arc;
    ///
    /// fn create_new_subscriber(node: Arc<Node>) -> Subscriber<std_msgs::msg::Bool> {
    ///     node.create_subscriber("topic_name", None).unwrap()
    /// }
    /// ```
    pub fn create_subscriber<T: TypeSupport>(
        self: &Arc<Self>,
        topic_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Subscriber<T>> {
        Subscriber::new(self.clone(), topic_name, qos)
    }

    /// Create a subscriber.
    /// If `qos` is specified `None`,
    /// the default profile is used.
    ///
    /// `T` is the type of messages the created subscriber receive.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{msg::common_interfaces::std_msgs, node::Node, topic::subscriber::Subscriber};
    /// use std::sync::Arc;
    ///
    /// fn create_subscriber_disable_loaned_message(node: Arc<Node>) -> Subscriber<std_msgs::msg::Bool> {
    ///     node.create_subscriber_disable_loaned_message("topic_name", None).unwrap()
    /// }
    /// ```
    pub fn create_subscriber_disable_loaned_message<T: TypeSupport>(
        self: &Arc<Self>,
        topic_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Subscriber<T>> {
        Subscriber::new_disable_loaned_message(self.clone(), topic_name, qos)
    }

    /// Create a server.
    /// If `qos` is specified `None`,
    /// the default profile is used.
    ///
    /// A server must receive `ServiceMsg::Request` and send `ServiceMsg::Response`.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{msg::common_interfaces::std_srvs, node::Node, service::server::Server};
    /// use std::sync::Arc;
    ///
    /// fn create_new_server(node: Arc<Node>) -> Server<std_srvs::srv::Empty> {
    ///     node.create_server("service_name", None).unwrap()
    /// }
    /// ```
    pub fn create_server<T: ServiceMsg>(
        self: &Arc<Self>,
        service_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Server<T>> {
        Server::new(self.clone(), service_name, qos)
    }

    /// Create a client.
    /// If `qos` is specified `None`,
    /// the default profile is used.
    ///
    /// A client must send `ServiceMsg::Request` and receive `ServiceMsg::Response`.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{msg::common_interfaces::std_srvs, node::Node, service::client::Client};
    /// use std::sync::Arc;
    ///
    /// fn create_new_client(node: Arc<Node>) -> Client<std_srvs::srv::Empty> {
    ///     node.create_client("service_name", None).unwrap()
    /// }
    /// ```
    pub fn create_client<T: ServiceMsg>(
        self: &Arc<Self>,
        service_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Client<T>> {
        Client::new(self.clone(), service_name, qos)
    }
}

impl Drop for Node {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_node_fini(&mut self.node);
    }
}

/// Options for nodes.
pub struct NodeOptions {
    options: rcl::rcl_node_options_t,
}

impl Default for NodeOptions {
    fn default() -> Self {
        let options = rcl::MTSafeFn::rcl_node_get_default_options();
        NodeOptions { options }
    }
}

impl NodeOptions {
    /// Create options to create a node
    pub fn new() -> Self {
        // TODO: allow setting options
        Default::default()
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_node_options_t {
        &self.options
    }
}

impl Drop for NodeOptions {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_node_options_fini(&mut self.options);
    }
}

unsafe impl Sync for Node {}
unsafe impl Send for Node {}
