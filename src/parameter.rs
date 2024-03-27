//! Parameter server.
//!
//! # Examples
//!
//! ## Wait update by callback
//!
//! ```
//! use safe_drive::{
//!     context::Context,
//!     logger::Logger,
//!     parameter::{ParameterServer, Value},
//!     pr_info,
//! };
//!
//! // Create a context and a node.
//! let ctx = Context::new().unwrap();
//! let node = ctx.create_node("param_server", None, Default::default()).unwrap();
//!
//! // Create a parameter server.
//! let param_server = node.create_parameter_server().unwrap();
//! {
//!     // Set parameters.
//!     let mut params = param_server.params.write(); // Write lock
//!
//!     // Statically typed parameter.
//!     params.set_parameter(
//!         "my_flag".to_string(),                     // parameter name
//!         Value::Bool(false),                        // value
//!         false,                                     // read only?
//!         Some("my flag's description".to_string()), // description
//!     ).unwrap();
//!
//!     // Dynamically typed parameter.
//!     params.set_dynamically_typed_parameter(
//!         "my_dynamic_type_flag".to_string(), // parameter name
//!         Value::Bool(false),                 // value
//!         false,                              // read only?
//!         Some("my dynamic type flag's description".to_string()), // description
//!     ).unwrap();
//!
//!     // Add Directly from Parameter struct
//!     let parameter_to_set = Parameter {
//!         Descriptor {
//!             Some("my parameter description".to_string()),                 // parameter description
//!             Some("my parameter addutional_constraints".to_string()),      // parameter additional constraints
//!             false,                                                                  // read only ?
//!             false,                                                                  // static or Dynamic
//!             None,                                                                   // floating point range
//!             None,                                                                   // integer point range
//!         },
//!         Value::Bool(false),                                                         // value
//!     }
//!     params.add_parameter(
//!         ("my parameter").to_string(),                                     // name
//!         parameter_to_set,                                                           // parameter
//!     )?;
//! }
//!
//! // Create a logger and a selector.
//! let logger = Logger::new("param_server");
//! let mut selector = ctx.create_selector().unwrap();
//!
//! // Add a callback function to the parameter server.
//! selector.add_parameter_server(
//!     param_server,
//!     Box::new(move |params, updated| {
//!         // Print updated parameters.
//!         let mut keys = String::new();
//!         for key in updated.iter() {
//!             let value = &params.get_parameter(key).unwrap().value;
//!             keys = format!("{keys}{key} = {}, ", value);
//!         }
//!         pr_info!(logger, "updated parameters: {keys}");
//!     }),
//! );
//!
//! // Do spin to wait update.
//! // loop {
//! //    selector.wait()?;
//! // }
//! ```
//!
//! ## Asynchronous wait
//!
//! ```
//! use safe_drive::{
//!     context::Context,
//!     error::DynError,
//!     logger::Logger,
//!     parameter::{ParameterServer, Value},
//!     pr_info,
//! };
//!
//! // Create a context and a node.
//! let ctx = Context::new().unwrap();
//! let node = ctx.create_node("async_param_server", None, Default::default()).unwrap();
//!
//! // Create a parameter server.
//! let mut param_server = node.create_parameter_server().unwrap();
//! {
//!     // Set parameters.
//!     let mut params = param_server.params.write(); // Write lock
//!
//!     // Statically typed parameter.
//!     params.set_parameter(
//!         "my_flag".to_string(),                     // parameter name
//!         Value::Bool(false),                        // value
//!         false,                                     // read only?
//!         Some("my flag's description".to_string()), // description
//!     ).unwrap();
//!
//!     // Dynamically typed parameter.
//!     params.set_dynamically_typed_parameter(
//!         "my_dynamic_type_flag".to_string(), // parameter name
//!         Value::Bool(false),                 // value
//!         false,                              // read only?
//!         Some("my dynamic type flag's description".to_string()), // description
//!     ).unwrap();
//! }
//!
//!     // Add Directly from Parameter struct
//!     let parameter_to_set = Parameter {
//!         Descriptor {
//!             Some(&quot;my parameter description&quot;.to_string()),                 // parameter description
//!             Some(&quot;my parameter addutional_constraints&quot;.to_string()),      // parameter additional constraints
//!             false,                                                                  // read only ?
//!             false,                                                                  // static or Dynamic
//!             None,                                                                   // floating point range
//!             None,                                                                   // integer point range
//!         },
//!         Value::Bool(false),                                                         // value
//!     }
//!     params.add_parameter(
//!         (&quot;my parameter&quot;).to_string(),                                     // name
//!         parameter_to_set,                                                           // parameter
//!     )?;
//! }
//!
//! async fn run_wait(mut param_server: ParameterServer) {
//!     loop {
//!         // Create a logger.
//!         let logger = Logger::new("async_param_server");
//!
//!         // Wait update asynchronously.
//!         let updated = param_server.wait().await.unwrap();
//!
//!         let params = param_server.params.read(); // Read lock
//!
//!         // Print updated parameters.
//!         let mut keys = String::new();
//!         for key in updated.iter() {
//!             let value = &params.get_parameter(key).unwrap().value;
//!             keys = format!("{keys}{key} = {}, ", value);
//!         }
//!         pr_info!(logger, "updated parameters: {keys}");
//!     }
//! }
//!
//! // async_std::task::block_on(run_wait(param_server)); // Spawn an asynchronous task.
//! ```

use crate::{
    error::{DynError, RCLResult},
    helper::Contains,
    is_halt,
    logger::{pr_error_in, pr_fatal_in, Logger},
    msg::{
        interfaces::rcl_interfaces::{
            self,
            msg::{
                ParameterDescriptor, ParameterDescriptorSeq, ParameterValue, ParameterValueSeq,
                SetParametersResultSeq,
            },
            srv::{
                DescribeParameters, DescribeParametersResponse, GetParameterTypes,
                GetParameterTypesResponse, GetParameters, GetParametersResponse, ListParameters,
                ListParametersResponse, SetParameters, SetParametersResponse,
            },
        },
        BoolSeq, F64Seq, I64Seq, RosString, RosStringSeq, U8Seq,
    },
    node::Node,
    qos::Profile,
    rcl::rcl_variant_t,
    selector::{
        async_selector::{Command, SELECTOR},
        guard_condition::GuardCondition,
        CallbackResult, Selector,
    },
    signal_handler::Signaled,
};
use num_traits::Zero;
use parking_lot::RwLock;
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    ffi::CStr,
    fmt::Display,
    future::Future,
    rc::Rc,
    slice::from_raw_parts,
    sync::Arc,
    task::Poll,
};

/// Parameter server.
///
/// # Example
///
/// ```
/// use safe_drive::{
///     context::Context,
///     parameter::{ParameterServer, Value},
/// };
///
/// // Create a context and a node.
/// let ctx = Context::new().unwrap();
/// let node = ctx.create_node("param_server_ex", None, Default::default()).unwrap();
///
/// // Create a parameter server.
/// let param_server = node.create_parameter_server().unwrap();
/// {
///     // Set parameters.
///     let mut params = param_server.params.write(); // Write lock
///
///     // Statically typed parameter.
///     params.set_parameter(
///         "my_flag".to_string(),                     // parameter name
///         Value::Bool(false),                        // value
///         false,                                     // read only?
///         Some("my flag's description".to_string()), // description
///     ).unwrap();
///
///     // Dynamically typed parameter.
///     params.set_dynamically_typed_parameter(
///         "my_dynamic_type_flag".to_string(), // parameter name
///         Value::Bool(false),                 // value
///         false,                              // read only?
///         Some("my dynamic type flag's description".to_string()), // description
///     ).unwrap();
/// }
///     // Add Directly from Parameter struct
///     let parameter_to_set = Parameter {
///         Descriptor {
///             Some(&quot;my parameter description&quot;.to_string()),                 // parameter description
///             Some(&quot;my parameter addutional_constraints&quot;.to_string()),      // parameter additional constraints
///             false,                                                                  // read only ?
///             false,                                                                  // static or Dynamic
///             None,                                                                   // floating point range
///             None,                                                                   // integer point range
///         },
///         Value::Bool(false),                                                         // value
///     }
///     params.add_parameter(
///         (&quot;my parameter&quot;).to_string(),                                     // name
///         parameter_to_set,                                                           // parameter
///     )?;
/// }
/// ```
pub struct ParameterServer {
    pub params: Arc<RwLock<Parameters>>,
    handler: Option<std::thread::JoinHandle<Result<(), DynError>>>,
    cond_halt: GuardCondition,
    pub(crate) cond_callback: GuardCondition,
    node: Arc<Node>,
}

/// Describe a range of integer.
///
/// # Example
///
/// ```
/// use safe_drive::{helper::Contains, parameter::IntegerRange};
/// let range = IntegerRange { min: -5, max: 10, step: 3 };
/// assert!(range.contains(-5));
/// assert!(range.contains(-2));
/// assert!(range.contains(10));
/// assert!(!range.contains(9));
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct IntegerRange {
    pub min: i64,
    pub max: i64,
    pub step: usize,
}

impl Contains for IntegerRange {
    type T = i64;
    fn contains(&self, val: i64) -> bool {
        let range = self.min..=self.max;
        if range.contains(&val) {
            let diff = val - self.min;
            (diff % self.step as i64) == 0
        } else {
            false
        }
    }
}

impl From<&IntegerRange> for rcl_interfaces::msg::IntegerRange {
    fn from(range: &IntegerRange) -> Self {
        rcl_interfaces::msg::IntegerRange {
            from_value: range.min,
            to_value: range.max,
            step: range.step as u64,
        }
    }
}

/// Describe a range of integer.
///
/// # Example
///
/// ```
/// use safe_drive::{helper::Contains, parameter::FloatingPointRange};
/// let range = FloatingPointRange { min: -5.0, max: 10.0, step: 3.0 };
/// assert!(range.contains(-5.0));
/// assert!(range.contains(-2.0));
/// assert!(range.contains(10.0));
/// assert!(!range.contains(9.0));
/// ```
#[derive(Debug, PartialEq, PartialOrd)]
pub struct FloatingPointRange {
    pub min: f64,
    pub max: f64,
    pub step: f64,
}

impl From<&FloatingPointRange> for rcl_interfaces::msg::FloatingPointRange {
    fn from(range: &FloatingPointRange) -> Self {
        rcl_interfaces::msg::FloatingPointRange {
            from_value: range.min,
            to_value: range.max,
            step: range.step,
        }
    }
}

impl Contains for FloatingPointRange {
    type T = f64;
    fn contains(&self, val: f64) -> bool {
        let range = self.min..=self.max;
        if range.contains(&val) {
            if self.step.is_zero() {
                return true;
            }

            let diff = val - self.min;
            (diff % self.step).is_zero()
        } else {
            false
        }
    }
}

#[derive(Debug)]
pub struct Descriptor {
    pub description: String,
    pub additional_constraints: String,
    pub read_only: bool,
    pub dynamic_typing: bool,
    pub floating_point_range: Option<FloatingPointRange>,
    pub integer_range: Option<IntegerRange>,
}

/// Parameters.
///
/// # Example
///
/// ```
/// use safe_drive::{error::DynError, parameter::{Parameters, Parameter, Value}};
///
/// fn get_param<'a>(params: &'a Parameters, name: &str) -> Option<&'a Parameter>
/// {
///     params.get_parameter(name)
/// }
///
/// fn set_param(params: &mut Parameters, name: String, value: Value) -> Result<(), DynError>
/// {
///     params.set_parameter(name, value, false /* read_only */, Some("description".to_string()))
/// }
/// ```
#[derive(Debug)]
pub struct Parameters {
    params: BTreeMap<String, Parameter>,
    updated: BTreeSet<String>,
}

impl Parameters {
    fn new() -> Self {
        Self {
            params: BTreeMap::new(),
            updated: BTreeSet::new(),
        }
    }

    pub(crate) fn take_updated(&mut self) -> BTreeSet<String> {
        std::mem::take(&mut self.updated)
    }

    pub fn get_parameter(&self, name: &str) -> Option<&Parameter> {
        self.params.get(name)
    }

    pub fn add_parameter(&mut self, name: String, parameter: Parameter) -> Result<(), DynError> {
        if let Some(_) = self.params.get_mut(&name) {
            let msg: String = format!("{} is already declared", name);
            Err(msg.into())
        } else {
            if parameter.check_range(&parameter.value) {
                self.params.insert(name, parameter);
                Ok(())
            } else {
                let msg = format!("{} is exceeding the range", name);
                return Err(msg.into());
            }
        }
    }

    pub fn set_parameter(
        &mut self,
        name: String,
        value: Value,
        read_only: bool,
        description: Option<String>,
    ) -> Result<(), DynError> {
        if value == Value::NotSet {
            Err("Value::NotSet cannot be used as a statically typed value".into())
        } else if let Some(param) = self.params.get_mut(&name) {
            if param.descriptor.dynamic_typing {
                let msg = format!("{} is a dynamically typed value", name);
                return Err(msg.into());
            }

            if param.descriptor.read_only {
                let msg = format!("{} is read only", name);
                return Err(msg.into());
            }

            if !param.check_range(&value) {
                let msg = format!("{} is exceeding the range", name);
                return Err(msg.into());
            }

            if param.value.type_check(&value) {
                param.value = value;
                Ok(())
            } else {
                let msg = format!(
                    "failed type checking: dst = {}, src = {}",
                    param.value.type_name(),
                    value.type_name()
                );
                Err(msg.into())
            }
        } else {
            let param = Parameter::new(
                value,
                read_only,
                false,
                description.unwrap_or_else(|| name.clone()),
            );
            self.params.insert(name, param);
            Ok(())
        }
    }

    pub fn set_dynamically_typed_parameter(
        &mut self,
        name: String,
        value: Value,
        read_only: bool,
        description: Option<String>,
    ) -> Result<(), DynError> {
        if let Some(param) = self.params.get_mut(&name) {
            if !param.descriptor.dynamic_typing {
                let msg = format!("{} is a statically typed value", name);
                return Err(msg.into());
            }

            if param.descriptor.read_only {
                let msg = format!("{} is read only", name);
                return Err(msg.into());
            }

            if !param.check_range(&value) {
                let msg = format!("{} is exceeding the range", name);
                return Err(msg.into());
            }

            param.value = value;
        } else {
            let param = Parameter::new(
                value,
                read_only,
                true,
                description.unwrap_or_else(|| name.clone()),
            );
            self.params.insert(name, param);
        }
        Ok(())
    }

    pub fn set_floating_point_range(
        &mut self,
        name: &str,
        min: f64,
        max: f64,
        step: f64,
    ) -> Result<(), DynError> {
        let range = FloatingPointRange { min, max, step };

        if let Some(param) = self.params.get_mut(name) {
            if !param.check_range(&param.value) {
                let msg = format!("{:?} is not in the range.", param.value);
                return Err(msg.into());
            }

            if param.descriptor.dynamic_typing {
                param.descriptor.floating_point_range = Some(range);
                Ok(())
            } else {
                match &param.value {
                    Value::F64(_) | Value::VecF64(_) => {
                        param.descriptor.floating_point_range = Some(range);
                        Ok(())
                    }
                    _ => {
                        let msg = format!(
                            "{}({}) is not a floating point (array) type.",
                            name,
                            param.value.type_name()
                        );
                        Err(msg.into())
                    }
                }
            }
        } else {
            let msg = format!("no such parameter: name = {}", name);
            Err(msg.into())
        }
    }

    pub fn set_integer_range(
        &mut self,
        name: &str,
        min: i64,
        max: i64,
        step: usize,
    ) -> Result<(), DynError> {
        let range = IntegerRange { min, max, step };

        if let Some(param) = self.params.get_mut(name) {
            if !param.check_range(&param.value) {
                let msg = format!("{:?} is not in the range.", param.value);
                return Err(msg.into());
            }

            if param.descriptor.dynamic_typing {
                param.descriptor.integer_range = Some(range);
                Ok(())
            } else {
                match &param.value {
                    Value::I64(_) | Value::VecI64(_) => {
                        param.descriptor.integer_range = Some(range);
                        Ok(())
                    }
                    _ => {
                        let msg = format!(
                            "{}({}) is not an integer (array) type.",
                            name,
                            param.value.type_name()
                        );
                        Err(msg.into())
                    }
                }
            }
        } else {
            let msg = format!("no such parameter: name = {}", name);
            Err(msg.into())
        }
    }
}

#[derive(Debug)]
pub struct Parameter {
    pub descriptor: Descriptor,
    pub value: Value,
}

impl Parameter {
    fn new(value: Value, read_only: bool, dynamic_typing: bool, description: String) -> Self {
        Self {
            descriptor: Descriptor {
                description,
                additional_constraints: "".to_string(),
                read_only,
                dynamic_typing,
                floating_point_range: None,
                integer_range: None,
            },
            value,
        }
    }

    fn check_range(&self, value: &Value) -> bool {
        match (value, &self.descriptor.integer_range) {
            (Value::I64(x), Some(range)) => return range.contains(*x),
            (Value::VecI64(arr), Some(range)) => return arr.iter().all(|x| range.contains(*x)),
            _ => (),
        }

        match (value, &self.descriptor.floating_point_range) {
            (Value::F64(x), Some(range)) => range.contains(*x),
            (Value::VecF64(arr), Some(range)) => return arr.iter().all(|x| range.contains(*x)),
            _ => true,
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd)]
pub enum Value {
    NotSet,
    Bool(bool),
    I64(i64),
    F64(f64),
    String(String),
    VecBool(Vec<bool>),
    VecI64(Vec<i64>),
    VecU8(Vec<u8>),
    VecF64(Vec<f64>),
    VecString(Vec<String>),
}

impl Value {
    fn type_check(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (Value::Bool(_), Value::Bool(_))
                | (Value::I64(_), Value::I64(_))
                | (Value::F64(_), Value::F64(_))
                | (Value::String(_), Value::String(_))
                | (Value::VecBool(_), Value::VecBool(_))
                | (Value::VecI64(_), Value::VecI64(_))
                | (Value::VecU8(_), Value::VecU8(_))
                | (Value::VecF64(_), Value::VecF64(_))
                | (Value::VecString(_), Value::VecString(_))
        )
    }

    fn type_name(&self) -> &str {
        match self {
            Value::Bool(_) => "Bool",
            Value::I64(_) => "I64",
            Value::F64(_) => "F64",
            Value::String(_) => "String",
            Value::VecBool(_) => "VecBool",
            Value::VecI64(_) => "VecI64",
            Value::VecU8(_) => "VecU8",
            Value::VecF64(_) => "VecF64",
            Value::VecString(_) => "VecString",
            Value::NotSet => "NotSet",
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(x) => write!(f, "{x}"),
            Value::I64(x) => write!(f, "{x}"),
            Value::F64(x) => write!(f, "{x}"),
            Value::String(x) => write!(f, "{x}"),
            Value::VecBool(x) => write!(f, "{:?}", x),
            Value::VecI64(x) => write!(f, "{:?}", x),
            Value::VecU8(x) => write!(f, "{:?}", x),
            Value::VecF64(x) => write!(f, "{:?}", x),
            Value::VecString(x) => write!(f, "{:?}", x),
            Value::NotSet => write!(f, "NotSet"),
        }
    }
}

impl From<&ParameterValue> for Value {
    fn from(var: &ParameterValue) -> Self {
        match var.type_ {
            1 => Value::Bool(var.bool_value),
            2 => Value::I64(var.integer_value),
            3 => Value::F64(var.double_value),
            4 => Value::String(var.string_value.to_string()),
            5 => {
                let mut v = Vec::new();
                var.byte_array_value.iter().for_each(|x| v.push(*x));
                Value::VecU8(v)
            }
            6 => {
                let mut v = Vec::new();
                var.bool_array_value.iter().for_each(|x| v.push(*x));
                Value::VecBool(v)
            }
            7 => {
                let mut v = Vec::new();
                var.integer_array_value.iter().for_each(|x| v.push(*x));
                Value::VecI64(v)
            }
            8 => {
                let mut v = Vec::new();
                var.double_array_value.iter().for_each(|x| v.push(*x));
                Value::VecF64(v)
            }
            9 => {
                let mut v = Vec::new();
                var.string_array_value
                    .iter()
                    .for_each(|x| v.push(x.to_string()));
                Value::VecString(v)
            }
            _ => Value::NotSet,
        }
    }
}

impl From<&Value> for ParameterValue {
    fn from(var: &Value) -> Self {
        let mut result = ParameterValue::new().unwrap();
        let logger = Logger::new("safe_drive");

        match var {
            Value::NotSet => result.type_ = 0,
            Value::Bool(val) => {
                result.type_ = 1;
                result.bool_value = *val;
            }
            Value::I64(val) => {
                result.type_ = 2;
                result.integer_value = *val;
            }
            Value::F64(val) => {
                result.type_ = 3;
                result.double_value = *val;
            }
            Value::String(val) => {
                result.type_ = 4;
                result.string_value = RosString::new(val).unwrap_or_else(|| {
                    pr_fatal_in!(logger, "{}:{}: failed allocation", file!(), line!());
                    RosString::null()
                });
            }
            Value::VecU8(val) => {
                result.type_ = 5;
                result.byte_array_value = U8Seq::new(val.len()).unwrap_or_else(|| {
                    pr_fatal_in!(logger, "{}:{}: failed allocation", file!(), line!());
                    U8Seq::null()
                });
                result
                    .byte_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| *dst = *src);
            }
            Value::VecBool(val) => {
                result.type_ = 6;
                result.bool_array_value = BoolSeq::new(val.len()).unwrap_or_else(|| {
                    pr_fatal_in!(logger, "{}:{}: failed allocation", file!(), line!());
                    BoolSeq::null()
                });
                result
                    .bool_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| *dst = *src);
            }
            Value::VecI64(val) => {
                result.type_ = 7;
                result.integer_array_value = I64Seq::new(val.len()).unwrap_or_else(|| {
                    pr_fatal_in!(logger, "{}:{}: failed allocation", file!(), line!());
                    I64Seq::null()
                });
                result
                    .integer_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| *dst = *src);
            }
            Value::VecF64(val) => {
                result.type_ = 8;
                result.double_array_value = F64Seq::new(val.len()).unwrap_or_else(|| {
                    pr_fatal_in!(logger, "{}:{}: failed allocation", file!(), line!());
                    F64Seq::null()
                });
                result
                    .double_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| *dst = *src);
            }
            Value::VecString(val) => {
                result.type_ = 9;
                result.string_array_value = RosStringSeq::new(val.len()).unwrap_or_else(|| {
                    pr_fatal_in!(logger, "{}:{}: failed allocation", file!(), line!());
                    RosStringSeq::null()
                });
                result
                    .string_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| {
                        dst.assign(src);
                    });
            }
        }
        result
    }
}

impl From<&rcl_variant_t> for Value {
    fn from(var: &rcl_variant_t) -> Self {
        if !var.bool_value.is_null() {
            Value::Bool(unsafe { *var.bool_value })
        } else if !var.integer_value.is_null() {
            Value::I64(unsafe { *var.integer_value })
        } else if !var.double_value.is_null() {
            Value::F64(unsafe { *var.double_value })
        } else if !var.string_value.is_null() {
            let s = unsafe { CStr::from_ptr(var.string_value) };
            Value::String(s.to_str().unwrap_or("").into())
        } else if !var.bool_array_value.is_null() {
            let v = &unsafe { *var.bool_array_value };
            let s = unsafe { from_raw_parts(v.values, v.size) };
            Value::VecBool(s.into())
        } else if !var.integer_array_value.is_null() {
            let v = &unsafe { *var.integer_array_value };
            let s = unsafe { from_raw_parts(v.values, v.size) };
            Value::VecI64(s.into())
        } else if !var.byte_array_value.is_null() {
            let v = &unsafe { *var.byte_array_value };
            let s = unsafe { from_raw_parts(v.values, v.size) };
            Value::VecU8(s.into())
        } else if !var.double_array_value.is_null() {
            let v = &unsafe { *var.double_array_value };
            let s = unsafe { from_raw_parts(v.values, v.size) };
            Value::VecF64(s.into())
        } else if !var.string_array_value.is_null() {
            let v = &unsafe { *var.string_array_value };
            let s = unsafe { from_raw_parts(v.data, v.size) };
            let s = s
                .iter()
                .map(|p| unsafe { CStr::from_ptr(*p).to_str().unwrap_or("").into() })
                .collect();
            Value::VecString(s)
        } else {
            Value::NotSet
        }
    }
}

impl ParameterServer {
    pub(crate) fn new(node: Arc<Node>) -> Result<Self, DynError> {
        let params_value = {
            let mut guard = crate::rcl::MT_UNSAFE_FN.lock();
            let fqn = node.get_fully_qualified_name()?;
            let arguments = unsafe { &mut (*node.context.as_ptr_mut()).global_arguments };
            guard.parameter_map(fqn.as_str(), arguments)?
        };
        let mut params = Parameters::new();
        for (k, v) in params_value.into_iter() {
            let _ = params.set_parameter(k, v, false, None);
        }
        let params = Arc::new(RwLock::new(params));
        let ps = params.clone();
        let n = node.clone();

        let cond_halt = GuardCondition::new(node.context.clone())?;
        let cond_halt_cloned = cond_halt.clone();

        let cond_callback = GuardCondition::new(node.context.clone())?;
        let cond_callback_cloned = cond_callback.clone();

        let handler =
            std::thread::spawn(move || param_server(n, ps, cond_halt_cloned, cond_callback_cloned));

        Ok(Self {
            params,
            handler: Some(handler),
            cond_halt,
            cond_callback,
            node,
        })
    }

    pub fn wait(&mut self) -> AsyncWait {
        AsyncWait {
            param_server: self,
            state: WaitState::Init,
        }
    }
}

impl Drop for ParameterServer {
    fn drop(&mut self) {
        if self.cond_halt.trigger().is_ok() {
            if let Some(handler) = self.handler.take() {
                let _ = handler.join();
            }
        }
    }
}

fn param_server(
    node: Arc<Node>,
    params: Arc<RwLock<Parameters>>,
    cond_halt: GuardCondition,
    cond_callback: GuardCondition,
) -> Result<(), DynError> {
    if let Ok(mut selector) = node.context.create_selector() {
        add_srv_list(&node, &mut selector, params.clone())?;
        add_srv_set(
            &node,
            &mut selector,
            params.clone(),
            "set_parameters",
            cond_callback.clone(),
        )?;
        add_srv_set(
            &node,
            &mut selector,
            params.clone(),
            "set_parameters_atomically",
            cond_callback,
        )?;
        add_srv_get(&node, &mut selector, params.clone())?;
        add_srv_get_types(&node, &mut selector, params.clone())?;
        add_srv_describe(&node, &mut selector, params)?;

        let is_halt = Rc::new(Cell::new(false));
        let is_halt_cloned = is_halt.clone();

        selector.add_guard_condition(
            &cond_halt,
            Some(Box::new(move || {
                is_halt_cloned.set(true);
                CallbackResult::Remove
            })),
            false,
        );

        while !is_halt.get() {
            selector.wait()?;
        }
    } else {
        let logger = Logger::new("safe_drive");
        pr_error_in!(logger, "failed to start a parameter server");
    }

    Ok(())
}

fn add_srv_set(
    node: &Arc<Node>,
    selector: &mut Selector,
    params: Arc<RwLock<Parameters>>,
    service_name: &str,
    cond_callback: GuardCondition,
) -> RCLResult<()> {
    let name = node.get_name()?;
    let srv_set = node.create_server::<SetParameters>(
        &format!("{name}/{service_name}"),
        Some(Profile::default()),
    )?;

    selector.add_server(
        srv_set,
        Box::new(move |req, _| {
            let mut results = if let Some(seq) = SetParametersResultSeq::new(req.parameters.len()) {
                seq
            } else {
                let response = SetParametersResponse::new().unwrap();
                return response;
            };

            let slice = results.as_slice_mut();

            let mut updated = 0;
            {
                let mut guard = params.write();
                for (i, param) in req.parameters.iter().enumerate() {
                    let key = param.name.to_string();
                    let val: Value = (&param.value).into();

                    if let Some(original) = guard.params.get_mut(&key) {
                        if original.descriptor.read_only {
                            let reason = format!("{} is read only", key);
                            slice[i].reason.assign(&reason);
                            continue;
                        }

                        if !original.check_range(&val) {
                            let reason = format!("{} is not in the range", key);
                            slice[i].reason.assign(&reason);
                            slice[i].successful = false;
                            continue;
                        }

                        if original.descriptor.dynamic_typing || original.value.type_check(&val) {
                            original.value = val;
                            slice[i].successful = true;
                            updated += 1;
                            guard.updated.insert(key);
                        } else {
                            let reason = format!(
                                "failed type checking: dst = {}, src = {}",
                                original.value.type_name(),
                                val.type_name()
                            );
                            slice[i].reason.assign(&reason);
                            slice[i].successful = false;
                        }
                    } else {
                        let reason = format!("no such parameter: name = {}", key);
                        slice[i].reason.assign(&reason);
                        slice[i].successful = false;
                    }
                }
            }

            if updated > 0 && cond_callback.trigger().is_err() {
                let logger = Logger::new("safe_drive");
                pr_fatal_in!(
                    logger,
                    "{}:{}: failed to trigger a condition variable",
                    file!(),
                    line!()
                );
            }

            let mut response = SetParametersResponse::new().unwrap();
            response.results = results;

            response
        }),
    );

    Ok(())
}

fn add_srv_get(
    node: &Arc<Node>,
    selector: &mut Selector,
    params: Arc<RwLock<Parameters>>,
) -> RCLResult<()> {
    let name = node.get_name()?;
    let srv_get = node.create_server::<GetParameters>(
        &format!("{name}/get_parameters"),
        Some(Profile::default()),
    )?;
    selector.add_server(
        srv_get,
        Box::new(move |req, _| {
            let mut result = Vec::new();

            let gurad = params.read();
            for name in req.names.iter() {
                let key = name.to_string();
                if let Some(param) = gurad.params.get(&key) {
                    result.push(&param.value);
                }
            }

            let mut response = GetParametersResponse::new().unwrap();

            if let Some(mut seq) = ParameterValueSeq::new(result.len()) {
                seq.iter_mut()
                    .zip(result.iter())
                    .for_each(|(dst, src)| *dst = (*src).into());
                response.values = seq;
            }

            response
        }),
    );

    Ok(())
}

macro_rules! unwrap_or_continue {
    ($e:expr) => {
        if let Some(x) = $e {
            x
        } else {
            continue;
        }
    };
}

fn add_srv_describe(
    node: &Arc<Node>,
    selector: &mut Selector,
    params: Arc<RwLock<Parameters>>,
) -> RCLResult<()> {
    let name = node.get_name()?;
    let srv_describe = node.create_server::<DescribeParameters>(
        &format!("{name}/describe_parameters"),
        Some(Profile::default()),
    )?;
    selector.add_server(
        srv_describe,
        Box::new(move |req, _| {
            let gurad = params.read();

            let mut results = Vec::new();
            for name in req.names.iter() {
                let key = name.to_string();
                if let Some(param) = gurad.params.get(&key) {
                    let value: ParameterValue = (&param.value).into();
                    let description =
                        unwrap_or_continue!(RosString::new(&param.descriptor.description));
                    let additional_constraints = unwrap_or_continue!(RosString::new(
                        &param.descriptor.additional_constraints
                    ));

                    let integer_range = if let Some(range) = &param.descriptor.integer_range {
                        let mut int_range =
                            unwrap_or_continue!(rcl_interfaces::msg::IntegerRangeSeq::new(1));
                        int_range.as_slice_mut()[0] = range.into();
                        int_range
                    } else {
                        unwrap_or_continue!(rcl_interfaces::msg::IntegerRangeSeq::new(0))
                    };

                    let floating_point_range = if let Some(range) =
                        &param.descriptor.floating_point_range
                    {
                        let mut f64_range =
                            unwrap_or_continue!(rcl_interfaces::msg::FloatingPointRangeSeq::new(1));
                        f64_range.as_slice_mut()[0] = range.into();
                        f64_range
                    } else {
                        unwrap_or_continue!(rcl_interfaces::msg::FloatingPointRangeSeq::new(0))
                    };

                    let result = ParameterDescriptor {
                        name: unwrap_or_continue!(RosString::new(&key)),
                        type_: value.type_,
                        description,
                        additional_constraints,
                        read_only: param.descriptor.read_only,
                        dynamic_typing: param.descriptor.dynamic_typing,
                        integer_range,
                        floating_point_range,
                    };
                    results.push(result);
                }
            }

            let mut response = DescribeParametersResponse::new().unwrap();
            if let Some(mut seq) = ParameterDescriptorSeq::new(results.len()) {
                seq.iter_mut()
                    .zip(results)
                    .for_each(|(dst, src)| *dst = src);
                response.descriptors = seq;
            };

            response
        }),
    );

    Ok(())
}

fn add_srv_get_types(
    node: &Arc<Node>,
    selector: &mut Selector,
    params: Arc<RwLock<Parameters>>,
) -> RCLResult<()> {
    let name = node.get_name()?;
    let srv_get_types = node.create_server::<GetParameterTypes>(
        &format!("{name}/get_parameter_types"),
        Some(Profile::default()),
    )?;
    selector.add_server(
        srv_get_types,
        Box::new(move |req, _| {
            let mut types = Vec::new();

            let gurad = params.read();
            for name in req.names.iter() {
                let key = name.to_string();
                if let Some(param) = gurad.params.get(&key) {
                    let v: ParameterValue = (&param.value).into();
                    types.push(v.type_);
                } else {
                    types.push(0);
                }
            }

            let mut response = GetParameterTypesResponse::new().unwrap();
            if let Some(mut seq) = U8Seq::new(types.len()) {
                seq.iter_mut()
                    .zip(types.iter())
                    .for_each(|(dst, src)| *dst = *src);
                response.types = seq;
            }

            response
        }),
    );

    Ok(())
}

fn add_srv_list(
    node: &Arc<Node>,
    selector: &mut Selector,
    params: Arc<RwLock<Parameters>>,
) -> RCLResult<()> {
    let name = node.get_name()?;
    let srv_list = node.create_server::<ListParameters>(
        &format!("{name}/list_parameters"),
        Some(Profile::default()),
    )?;
    selector.add_server(
        srv_list,
        Box::new(move |req, _| {
            let separator = b'.';

            let mut result = Vec::new();
            let mut result_prefix = Vec::new();
            let prefixes: Vec<String> = req
                .prefixes
                .iter()
                .map(|prefix| prefix.get_string())
                .collect();

            let guard = params.write();

            for (k, _v) in guard.params.iter() {
                let cnt = k.as_bytes().iter().filter(|c| **c == separator).count();
                let get_all = prefixes.is_empty() && req.depth == 0 || cnt < req.depth as usize;

                let matches = prefixes.iter().find(|prefix| {
                    if k == *prefix {
                        true
                    } else {
                        let mut prefix_sep = (*prefix).clone();
                        prefix_sep.push(separator as char);

                        if k.starts_with(&prefix_sep) {
                            if req.depth == 0 {
                                true
                            } else {
                                let cnt = k.as_bytes()[..prefix.len()]
                                    .iter()
                                    .filter(|c| **c == separator)
                                    .count();
                                req.depth == 0 || cnt < req.depth as usize
                            }
                        } else {
                            false
                        }
                    }
                });

                if get_all || matches.is_some() {
                    result.push(k);
                    let separated: Vec<_> = k.split(separator as char).collect();
                    if separated.len() > 1 {
                        let prefix = separated[..separated.len() - 1].iter().fold(
                            String::new(),
                            |mut s, item| {
                                s.push_str(item);
                                s
                            },
                        );
                        if !result_prefix.contains(&prefix) {
                            result_prefix.push(prefix);
                        }
                    }
                }
            }

            let mut response = ListParametersResponse::new().unwrap();
            if let (Some(mut seq_names), Some(mut seq_prefixes)) = (
                RosStringSeq::<0, 0>::new(result.len()),
                RosStringSeq::<0, 0>::new(result_prefix.len()),
            ) {
                seq_names
                    .iter_mut()
                    .zip(result.iter())
                    .for_each(|(dst, src)| {
                        dst.assign(src);
                    });

                seq_prefixes
                    .iter_mut()
                    .zip(result_prefix.iter())
                    .for_each(|(dst, src)| {
                        dst.assign(src);
                    });

                response.result.names = seq_names;
                response.result.prefixes = seq_prefixes;
            }

            response
        }),
    );

    Ok(())
}

#[derive(Clone, Copy, Debug)]
enum WaitState {
    Init,
    Waiting,
}

pub struct AsyncWait<'a> {
    param_server: &'a ParameterServer,
    state: WaitState,
}

impl<'a> Future for AsyncWait<'a> {
    type Output = Result<BTreeSet<String>, DynError>;
    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        match self.state {
            WaitState::Init => {
                let mut waker = Some(cx.waker().clone());
                let mut guard = SELECTOR.lock();

                if let Err(e) = guard.send_command(
                    &self.param_server.node.context,
                    Command::ConditionVar(
                        self.param_server.cond_callback.clone(),
                        Box::new(move || {
                            let w = waker.take().unwrap();
                            w.wake();
                            CallbackResult::Remove
                        }),
                    ),
                ) {
                    Poll::Ready(Err(e))
                } else {
                    self.get_mut().state = WaitState::Waiting;
                    Poll::Pending
                }
            }
            WaitState::Waiting => {
                let mut guard = self.param_server.params.write();
                let updated = guard.take_updated();
                Poll::Ready(Ok(updated))
            }
        }
    }
}

impl<'a> Drop for AsyncWait<'a> {
    fn drop(&mut self) {
        let mut guard = SELECTOR.lock();
        if guard
            .send_command(
                &self.param_server.node.context,
                Command::RemoveConditionVar(self.param_server.cond_callback.clone()),
            )
            .is_err()
        {}
    }
}
