# Parameter

[Source code](https://github.com/tier4/safe_drive_tutorial/tree/main/params).

This chapter introduces how to use parameters.
A node can have parameters as follows.

 ```mermaid
graph TD;
    NodeA --> ParamA1:i64;
    NodeA --> ParamA2:bool;
    NodeA --> ParamA3:String;
    NodeB --> ParamB1:f64;
    NodeB --> ParamB2:f64;
```

In this figure, NodeA has 3 parameters whose types are
`i64`, `bool`, and `String`, respectively,
and NodeB has 2 parameters whose types are `f64`.
Parameters can be read/write from external nodes.

To receive a notification of updating a parameter,
we can use a callback function or async/await.
In this chapter, we will explain how to handle it.

## Packages

We will prepare 2 packages as follows.

```text
$ mkdir params
$ cd params
$ cargo new param_server
$ cargo new async_param_server
```

`param_server` explains a callback based parameter handling, and `async_param_server` explains an async/await based.

To manage 2 packages, let's prepare `Cargo.toml` file for a workspace as follows.

`params/Cargo.toml`

```toml
[workspace]
members = ["param_server", "async_param_server"]
```

The following table shows files we use in this chapter.

|File                       | What?                              |
|---------------------------|------------------------------------|
|params/param_server/       | callback based parameter server    |
|params/async_param_server/ | async/await based parameter server |
|params/Cargo.toml          | workspace configuration            |

## Type of Parameter

Before explaining handlers,
let's see types of parameters.

The type of parameter value is defined by `safe_drive::parameter::Value` as follows.

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

This means that `i64` is valid,
but `i8`, `i32`, and other user defined types are invalid.

A parameter is associated with a descriptor of `safe_drive::parameter::Descriptor` as follows.

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

So, a parameter and parameters can be represented by `safe_drive::parameter::{Parameter, Parameters}` as follows.

```rust
pub struct Parameter {
    pub descriptor: Descriptor,
    pub value: Value,
}

pub struct Parameters { /* omitted private fields */ }
```

and a parameter server can be represented by
`safe_drive::parameter::ParameterServer` as follows.

```rust
pub struct ParameterServer {
    pub params: Arc<RwLock<Parameters>>
    // omitted private fields
}
```

In summary, a parameter server can be represented as follows.

 ```mermaid
graph TD;
    ParameterServer --> Parameters;
    Parameters --> Parameter;
    Parameter --> Descriptor;
    Parameter --> Value;
```

## Parameter Setting and Waiting Update by Callback

We will explain how to set parameters,
and how to wait updating by using a callback function.

### Edit `param_server/Cargo.toml`

Add `safe_drive` to the dependencies section of `Cargo.toml` as follows.

```toml
[dependencies]
safe_drive = "0.2"
```

### Edit `param_server/src/main.rs`

`param_server` can be implemented as follows.
This sets 2 parameters up and waits updating.

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

### `param_server` in Detail

First of all, we have to create a parameter server by `create_parameter_server()` method as follows.

```rust
// Create a parameter server.
let param_server = node.create_parameter_server()?;
```

Then set parameters as follows.
To update parameters, we have to acquire a write lock
for mutual exclusion by `write()` method.

```rust
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
```

To set a statically typed parameters, use `set_parameter()`.
A statically typed parameter cannot be updated
by a value whose type is different from original type.

To set a dynamically typed parameters, use `set_dynamically_typed_parameter()`.
A dynamically typed parameter can be updated by an arbitrary type.

Finally, register a callback function to wait updating
parameters as follows.

```rust
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
```

1st argument of the closure, `params`, is a value of parameters,
and 2nd argument, `updated` is a value containing updated parameters.

### Execute `param_server`

Then, let's execute `param_server` and get/set a parameter.
First, execute `param_server` in a terminal application window as follows.

```text
$ cargo run --bin param_server
    Finished dev [unoptimized + debuginfo] target(s) in 0.01s
     Running `target/debug/param_server`
[INFO] [1669873997.622330908] [param_server]: updated parameters: my_flag = true,
```

Then, get and set the parameter by using `ros2` command in another terminal application window as follows.

```text
$ ros2 param get param_server my_flag
Boolean value is: False
$ ros2 param set param_server my_flag True
Set parameter successful
$ ros2 param get param_server my_flag
Boolean value is: True
$ ros2 param set param_server my_flag 10
Setting parameter failed: failed type checking: dst = Bool, src = I64
```

We can get and set boolean values,
but integer value cannot be set because `my_flag` is boolean type
and statically typed.

---

## Asynchronous Wait

Then, we explain async/await based parameter server.

### Edit `async_param_server/Cargo.toml`

Add `safe_drive` and `tokio` to the dependencies section of `Cargo.toml` as follows.

```toml
[dependencies]
safe_drive = "0.2"
tokio = { version = "1", features = ["full"] }
```

### Edit `async_param_server/src/main.rs`

`async_param_server` can be implemented as follows.
This sets 2 parameters up and waits updating.

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

Important things are only following 2 lines.

```rust
// Wait update asynchronously.
let updated = param_server.wait().await?;

let params = param_server.params.read(); // Read lock
```

To wait updating, use `wait().await`
and acquire a read lock by `read()` method
to read parameters.
`wait().await` returns updated parameters.
