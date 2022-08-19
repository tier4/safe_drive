use crate::{
    error::{DynError, RCLResult},
    logger::{pr_error_in, Logger},
    msg::{
        interfaces::rcl_interfaces::{
            msg::{ParameterValue, ParameterValueSeq, SetParametersResultSeq},
            srv::{
                GetParameters, GetParametersResponse, ListParameters, ListParametersResponse,
                SetParameters, SetParametersResponse,
            },
        },
        BoolSeq, F64Seq, I64Seq, RosString, RosStringSeq, U8Seq,
    },
    node::Node,
    qos::Profile,
    rcl::rcl_variant_t,
    selector::{guard_condition::GuardCondition, CallbackResult, Selector},
};
use parking_lot::RwLock;
use std::{cell::Cell, collections::BTreeMap, ffi::CStr, rc::Rc, slice::from_raw_parts, sync::Arc};

pub struct ParameterServer {
    pub params: Arc<RwLock<BTreeMap<String, Value>>>,
    handler: Option<std::thread::JoinHandle<Result<(), DynError>>>,
    cond: Arc<GuardCondition>,
    _node: Arc<Node>,
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
        match (self, other) {
            (Value::Bool(_), Value::Bool(_)) => true,
            (Value::I64(_), Value::I64(_)) => true,
            (Value::F64(_), Value::F64(_)) => true,
            (Value::String(_), Value::String(_)) => true,
            (Value::VecBool(_), Value::VecBool(_)) => true,
            (Value::VecI64(_), Value::VecI64(_)) => true,
            (Value::VecU8(_), Value::VecU8(_)) => true,
            (Value::VecF64(_), Value::VecF64(_)) => true,
            (Value::VecString(_), Value::VecString(_)) => true,
            _ => false,
        }
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
                result.string_value = RosString::new(&val).unwrap();
            }
            Value::VecU8(val) => {
                result.type_ = 5;
                result.byte_array_value = U8Seq::new(val.len()).unwrap();
                result
                    .byte_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| *dst = *src);
            }
            Value::VecBool(val) => {
                result.type_ = 6;
                result.bool_array_value = BoolSeq::new(val.len()).unwrap();
                result
                    .bool_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| *dst = *src);
            }
            Value::VecI64(val) => {
                result.type_ = 7;
                result.integer_array_value = I64Seq::new(val.len()).unwrap();
                result
                    .integer_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| *dst = *src);
            }
            Value::VecF64(val) => {
                result.type_ = 8;
                result.double_array_value = F64Seq::new(val.len()).unwrap();
                result
                    .double_array_value
                    .iter_mut()
                    .zip(val.iter())
                    .for_each(|(dst, src)| *dst = *src);
            }
            Value::VecString(val) => {
                result.type_ = 9;
                result.string_array_value = RosStringSeq::new(val.len()).unwrap();
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
            return Value::Bool(unsafe { *var.bool_value });
        } else if !var.integer_value.is_null() {
            return Value::I64(unsafe { *var.integer_value });
        } else if !var.double_value.is_null() {
            return Value::F64(unsafe { *var.double_value });
        } else if !var.string_value.is_null() {
            let s = unsafe { CStr::from_ptr(var.string_value) };
            return Value::String(s.to_str().unwrap_or("").into());
        } else if !var.bool_array_value.is_null() {
            let v = &unsafe { *var.bool_array_value };
            let s = unsafe { from_raw_parts(v.values, v.size as usize) };
            return Value::VecBool(s.into());
        } else if !var.integer_array_value.is_null() {
            let v = &unsafe { *var.integer_array_value };
            let s = unsafe { from_raw_parts(v.values, v.size as usize) };
            return Value::VecI64(s.into());
        } else if !var.byte_array_value.is_null() {
            let v = &unsafe { *var.byte_array_value };
            let s = unsafe { from_raw_parts(v.values, v.size as usize) };
            return Value::VecU8(s.into());
        } else if !var.double_array_value.is_null() {
            let v = &unsafe { *var.double_array_value };
            let s = unsafe { from_raw_parts(v.values, v.size as usize) };
            return Value::VecF64(s.into());
        } else if !var.string_array_value.is_null() {
            let v = &unsafe { *var.string_array_value };
            let s = unsafe { from_raw_parts(v.data, v.size as usize) };
            let s = s
                .into_iter()
                .map(|p| unsafe { CStr::from_ptr(*p).to_str().unwrap_or("").into() })
                .collect();
            return Value::VecString(s);
        } else {
            Value::NotSet
        }
    }
}

impl ParameterServer {
    pub fn new(node: Arc<Node>) -> RCLResult<Self> {
        let params = Arc::new(RwLock::new(BTreeMap::new()));
        let ps = params.clone();
        let n = node.clone();
        let cond = GuardCondition::new(node.context.clone())?;
        let cond_cloned = cond.clone();
        let handler = std::thread::spawn(move || param_server(n, ps, cond_cloned));

        Ok(Self {
            params: params,
            handler: Some(handler),
            cond,
            _node: node,
        })
    }
}

impl Drop for ParameterServer {
    fn drop(&mut self) {
        if self.cond.trigger().is_ok() {
            if let Some(handler) = self.handler.take() {
                let _ = handler.join();
            }
        }
    }
}

fn param_server(
    node: Arc<Node>,
    params: Arc<RwLock<BTreeMap<String, Value>>>,
    guard: Arc<GuardCondition>,
) -> Result<(), DynError> {
    if let Ok(mut selector) = node.context.create_selector() {
        add_srv_list(&node, &mut selector, params.clone())?;
        add_srv_set(&node, &mut selector, params.clone(), "set_parameters")?;
        add_srv_set(
            &node,
            &mut selector,
            params.clone(),
            "set_parameters_atomically",
        )?;
        add_srv_get(&node, &mut selector, params)?;

        let is_halt = Rc::new(Cell::new(false));
        let is_halt_cloned = is_halt.clone();

        selector.add_guard_condition(
            guard.as_ref(),
            Some(Box::new(move || {
                is_halt_cloned.set(true);
                CallbackResult::Remove
            })),
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
    params: Arc<RwLock<BTreeMap<String, Value>>>,
    service_name: &str,
) -> RCLResult<()> {
    let name = node.get_name();
    let srv_set = node.create_server::<SetParameters>(
        &format!("{name}/{service_name}"),
        Some(Profile::default()),
    )?;

    selector.add_server(
        srv_set,
        Box::new(move |req, _| {
            let mut results = SetParametersResultSeq::new(req.parameters.len()).unwrap();
            let slice = results.as_slice_mut();

            let mut guard = params.write();
            for (i, param) in req.parameters.iter().enumerate() {
                let key = param.name.to_string();
                let val: Value = (&param.value).into();

                if let Some(original) = guard.get_mut(&key) {
                    if original.type_check(&val) {
                        *original = val;
                        slice[i].successful = true;
                    } else {
                        slice[i].successful = false;
                        let reason = format!(
                            "failed type checking: dst = {}, src = {}",
                            original.type_name(),
                            val.type_name()
                        );
                        slice[i].reason.assign(&reason);
                    }
                } else {
                    slice[i].successful = false;
                    let reason = format!("no such parameter: name = {}", key);
                    slice[i].reason.assign(&reason);
                }
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
    params: Arc<RwLock<BTreeMap<String, Value>>>,
) -> RCLResult<()> {
    let name = node.get_name();
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
                if let Some(value) = gurad.get(&key) {
                    result.push(value);
                }
            }

            let mut response = GetParametersResponse::new().unwrap();
            response.values = ParameterValueSeq::new(result.len()).unwrap();

            response
                .values
                .iter_mut()
                .zip(result.iter())
                .for_each(|(dst, src)| *dst = (*src).into());

            response
        }),
    );

    Ok(())
}

fn add_srv_list(
    node: &Arc<Node>,
    selector: &mut Selector,
    params: Arc<RwLock<BTreeMap<String, Value>>>,
) -> RCLResult<()> {
    let name = node.get_name();
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

            for (k, _v) in guard.iter() {
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
            response.result.names = RosStringSeq::<0, 0>::new(result.len()).unwrap();
            response
                .result
                .names
                .iter_mut()
                .zip(result.iter())
                .for_each(|(dst, src)| {
                    dst.assign(src);
                });

            response.result.prefixes = RosStringSeq::<0, 0>::new(result_prefix.len()).unwrap();
            response
                .result
                .prefixes
                .iter_mut()
                .zip(result_prefix.iter())
                .for_each(|(dst, src)| {
                    dst.assign(src);
                });

            response
        }),
    );

    Ok(())
}
