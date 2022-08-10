use crate::{
    error::RCLResult,
    logger::{pr_error_in, Logger},
    msg::{
        interfaces::rcl_interfaces::srv::{ListParameters, ListParametersResponse},
        RosStringSeq,
    },
    node::Node,
    qos::Profile,
    rcl::rcl_variant_t,
    selector::Selector,
};
use parking_lot::Mutex;
use std::{collections::BTreeMap, ffi::CStr, slice::from_raw_parts, sync::Arc};

pub struct Parameters {
    params: Arc<Mutex<BTreeMap<String, Value>>>,
    node: Arc<Node>,
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

impl Parameters {
    fn new(node: Arc<Node>) -> RCLResult<Self> {
        let params = Arc::new(Mutex::new(BTreeMap::new()));
        let ps = params.clone();
        let n = node.clone();

        std::thread::spawn(move || param_server(n, ps));

        Ok(Self {
            params: params,
            node,
        })
    }
}

fn param_server(node: Arc<Node>, params: Arc<Mutex<BTreeMap<String, Value>>>) -> RCLResult<()> {
    if let Ok(mut selector) = node.context.create_selector() {
        add_srv_list(&node, &mut selector, params)?;
    } else {
        let logger = Logger::new("safe_drive");
        pr_error_in!(logger, "");
    }

    Ok(())
}

fn add_srv_list(
    node: &Arc<Node>,
    selector: &mut Selector,
    params: Arc<Mutex<BTreeMap<String, Value>>>,
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
                .as_slice()
                .iter()
                .map(|prefix| prefix.get_string())
                .collect();

            let guard = params.lock();

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
                .as_slice_mut()
                .iter_mut()
                .zip(result.iter())
                .for_each(|(dst, src)| {
                    dst.assign(src);
                });

            response.result.prefixes = RosStringSeq::<0, 0>::new(result_prefix.len()).unwrap();
            response
                .result
                .prefixes
                .as_slice_mut()
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
