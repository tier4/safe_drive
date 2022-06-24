# Publish and Subscribe

This chapter introduces a simple example of publish and subscribe communication.
This communication is so-called topic by ROS2.
There are `N` senders and `M` receivers in a topic.
This tutorial implements 1 sender (in Rust) and 2 receivers (in Rust and C++).

## Directories

First of all, create working directories as follows.

```shell
$ mkdir ros2rust
$ mkdir ros2rust/src
```

Following directories are important directories
we will create throughout this tutorial.

| Directories                  | What?             |
|------------------------------|-------------------|
| ros2rust/src/my_talker       | sender in Rust    |
| ros2rust/src/my_listener     | receiver in Rust  |
| ros2rust/src/my_cpp_listener | receiver in C++   |
| ros2rust/install             | created by colcon |

## Talker in Rust

```shell
$ cd ros2rust/src
$ cargo new my_talker
```

```toml
# Cargo.toml
[dependencies]
safe_drive = { path = "path_to/safe_drive" }
```

```rust
// ros2rust/src/my_talker/src/main.rs
use safe_drive::{context::Context, error::DynError, msg::common_interfaces::std_msgs};
use std::time::Duration;

fn main() -> Result<(), DynError> {
    // Create a context.
    let ctx = Context::new()?;

    // Create a node.
    let node = ctx.create_node("my_node", None, Default::default())?;

    // Create a publisher.
    let publisher = node.create_publisher::<std_msgs::msg::String>("my_topic", None)?;

    let mut cnt = 0; // Counter.
    loop {
        // Create a message to be sent.
        let data = format!("Hello, World!: cnt = {cnt}");
        let mut msg = std_msgs::msg::String::new().unwrap();
        msg.data.assign(&data);

        // Send a message.
        publisher.send(msg)?;

        // Sleep 1s.
        cnt += 1;
        std::thread::sleep(Duration::from_secs(1));
    }
}
```


## Listener in Rust

## Listener in C++
