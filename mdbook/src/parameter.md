# Parameter

```text
$ mkdir params
$ cd params
$ cargo new param_server
$ cargo new async_param_server
```

```toml
# params/Cargo.toml
[workspace]
members = ["param_server", "async_param_server"]
```

## Type of Parameter

`safe_drive::parameter::Value`

```rust
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
```

`safe_drive::parameter::Descriptor`

```rust
pub struct Descriptor {
    pub description: String,
    pub additional_constraints: String,
    pub read_only: bool,
    pub dynamic_typing: bool,
    pub floating_point_range: Option<FloatingPointRange>,
    pub integer_range: Option<IntegerRange>,
}
```

`safe_drive::parameter::{Parameter, Parameters, ParameterServer}`

```rust
pub struct Parameter {
    pub descriptor: Descriptor,
    pub value: Value,
}

pub struct Parameters { /* omitted private fields */ }

pub struct ParameterServer {
    pub params: Arc<RwLock<Parameters>>
    // omitted private fields
}
```

## Parameter Setting and Waiting Update by Callback

```rust
use safe_drive::{context::Context, error::DynError, logger::Logger, parameter::Value, pr_info};

fn main() -> Result<(), DynError> {
    // Create a context and a node.
    let ctx = Context::new()?;
    let node = ctx.create_node("param_server", None, Default::default())?;

    // Create a parameter server.
    let param_server = node.create_parameter_server()?;
    {
        // Set parameters.
        let mut params = param_server.params.write(); // Write lock

        // Statically typed parameter.
        params.set_parameter(
            "my_flag".to_string(),                     // parameter name
            Value::Bool(false),                        // value
            false,                                     // read only?
            Some("my flag's description".to_string()), // description
        )?;

        // Dynamically typed parameter.
        params.set_dynamically_typed_parameter(
            "my_dynamic_type_flag".to_string(), // parameter name
            Value::Bool(false),                 // value
            false,                              // read only?
            Some("my dynamic type flag's description".to_string()), // description
        )?;
    }

    // Create a logger and a selector.
    let logger = Logger::new("param_server");
    let mut selector = ctx.create_selector()?;

    // Add a callback function to the parameter server.
    selector.add_parameter_server(
        param_server,
        Box::new(move |params, updated| {
            // Print updated parameters.
            let mut keys = String::new();
            for key in updated.iter() {
                let value = &params.get_parameter(key).unwrap().value;
                keys = format!("{keys}{key} = {}, ", value);
            }
            pr_info!(logger, "updated parameters: {keys}");
        }),
    );

    // Spin.
    loop {
        selector.wait()?;
    }
}
```

## Asynchronous Wait

```rust
use safe_drive::{context::Context, error::DynError, logger::Logger, parameter::Value, pr_info};

#[tokio::main]
async fn main() -> Result<(), DynError> {
    // Create a context and a node.
    let ctx = Context::new()?;
    let node = ctx.create_node("async_param_server", None, Default::default())?;

    // Create a parameter server.
    let mut param_server = node.create_parameter_server()?;
    {
        // Set parameters.
        let mut params = param_server.params.write(); // Write lock

        // Statically typed parameter.
        params.set_parameter(
            "my_flag".to_string(),                     // parameter name
            Value::Bool(false),                        // value
            false,                                     // read only?
            Some("my flag's description".to_string()), // description
        )?;

        // Dynamically typed parameter.
        params.set_dynamically_typed_parameter(
            "my_dynamic_type_flag".to_string(), // parameter name
            Value::Bool(false),                 // value
            false,                              // read only?
            Some("my dynamic type flag's description".to_string()), // description
        )?;
    }

    // Create a logger.
    let logger = Logger::new("async_param_server");

    loop {
        // Wait update asynchronously.
        let updated = param_server.wait().await?;

        let params = param_server.params.read(); // Read lock

        // Print updated parameters.
        let mut keys = String::new();
        for key in updated.iter() {
            let value = &params.get_parameter(key).unwrap().value;
            keys = format!("{keys}{key} = {}, ", value);
        }
        pr_info!(logger, "updated parameters: {keys}");
    }
}
```
