# Publish and Subscribe

This chapter introduces a simple example of publish and subscribe communication.
This communication is so-called topic by ROS2.
There are `N` senders and `M` receivers in a topic.
This tutorial implements 1 sender (in Rust) and 2 receivers (in Rust and C++).

## Directories

First of all, create working directories as follows.

```text
$ mkdir ros2rust
$ mkdir ros2rust/src
```

Following directories are important directories
we will create throughout this tutorial.

| Directories                  | What?             |
|------------------------------|-------------------|
| ros2rust/src/my_talker       | sender in Rust    |
| ros2rust/src/my_listener     | receiver in Rust  |
| ros2rust/install             | created by colcon |

## Talker in Rust

```text
$ cd ros2rust/src
$ cargo new my_talker
```

We create and edit files as follows.

| Files                 | What?                                |
|-----------------------|--------------------------------------|
| my_talker/Cargo.toml  | for Cargo                            |
| my_talker/build.rs    | to specify library path for a linker |
| my_talker/package.xml | for ROS2                             |
| my_talker/src/main.rs | source code                          |

### Edit `my_talker/Cargo.toml`

Add safe_drive to the dependencies.

```toml
# ros2rust/src/my_talker/Cargo.toml
[dependencies]
safe_drive = { path = "path_to/safe_drive" }
```

### Edit `my_talker/src/main.rs`

```rust
// ros2rust/src/my_talker/src/main.rs
use safe_drive::{
    context::Context, error::DynError, logger::Logger,
    msg::common_interfaces::std_msgs, pr_info
};
use std::time::Duration;

fn main() -> Result<(), DynError> {
    // Create a context.
    let ctx = Context::new()?;

    // Create a node.
    let node = ctx.create_node("my_talker", None, Default::default())?;

    // Create a publisher.
    let publisher = node.create_publisher::<std_msgs::msg::String>("my_topic", None)?;

    // Create a logger.
    let logger = Logger::new("my_talker");

    let mut cnt = 0; // Counter.
    let mut msg = std_msgs::msg::String::new().unwrap();
    loop {
        // Create a message to be sent.
        let data = format!("Hello, World!: cnt = {cnt}");
        msg.data.assign(&data);

        pr_info!(logger, "send: {}", msg.data); // Print log.

        // Send a message.
        publisher.send(&msg)?;

        // Sleep 1s.
        cnt += 1;
        std::thread::sleep(Duration::from_secs(1));
    }
}
```

### Create `my_talker/build.rs`

```rust
// ros2rust/src/my_talker/build.rs
fn main() {
    if let Some(e) = std::env::var_os("AMENT_PREFIX_PATH") {
        let env = e.to_str().unwrap();
        for path in env.split(":") {
            println!("cargo:rustc-link-search={path}/lib");
        }
    }
}
```

### Create `my_talker/package.xml`

```xml
<!-- ros2rust/src/my_talker/package.xml -->
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>my_talker</name>
  <version>0.0.0</version>
  <description>My Talker in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

### Execute The Talker

```text
$ . /opt/ros/galactic/setup.bash
```

```text
$ cd ros2rust
$ colcon build --cargo-args --release
```

```text
$ . ./install/setup.bash
$ ros2 run my_talker my_talker
[INFO] [1656048392.368568500] [my_talker]: send: Hello, World!: cnt = 0
[INFO] [1656048393.368787500] [my_talker]: send: Hello, World!: cnt = 1
[INFO] [1656048394.368994200] [my_talker]: send: Hello, World!: cnt = 2
```

## Listener in Rust

```text
$ cd ros2rust/src
$ cargo new my_listener
```

| Files                   | What?                                |
|-------------------------|--------------------------------------|
| my_listener/Cargo.toml  | for Cargo                            |
| my_listener/build.rs    | to specify library path for a linker |
| my_listener/package.xml | for ROS2                             |
| my_listener/src/main.rs | source code                          |

### Edit `my_listener/Cargo.toml`

```toml
# ros2rust/src/my_listener/Cargo.toml
[dependencies]
safe_drive = { path = "path_to/safe_drive" }
```

### Edit `my_listener/src/main.rs`

```rust
// ros2rust/src/my_listener/src/main.rs
use safe_drive::{
    context::Context, error::DynError, logger::Logger,
    msg::common_interfaces::std_msgs, pr_info,
};

fn main() -> Result<(), DynError> {
    // Create a context.
    let ctx = Context::new()?;

    // Create a node.
    let node = ctx.create_node("my_listener", None, Default::default())?;

    // Create a subscriber.
    let subscriber = node.create_subscriber::<std_msgs::msg::String>("my_topic", None)?;

    // Create a logger.
    let logger = Logger::new("my_listener");

    // Create a selector.
    let mut selector = ctx.create_selector()?;

    // Add a callback function.
    selector.add_subscriber(
        subscriber,
        Box::new(move |msg| {
            pr_info!(logger, "receive: {}", msg.data);
        }),
        false,
    );

    // Spin.
    loop {
        selector.wait()?;
    }
}
```

### Create `my_listener/build.rs`

```rust
// ros2rust/src/my_talker/build.rs
fn main() {
    if let Some(e) = std::env::var_os("AMENT_PREFIX_PATH") {
        let env = e.to_str().unwrap();
        for path in env.split(":") {
            println!("cargo:rustc-link-search={path}/lib");
        }
    }
}
```

### Create `my_listener/package.xml`

```xml
<!-- ros2rust/src/my_listener/package.xml -->
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>my_listener</name>
  <version>0.0.0</version>
  <description>My Listener in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

### Execute The Listener

```text
$ cd ros2rust
$ colcon build --cargo-args --release
```

```text
$ . ./install/setup.bash
$ ros2 run my_talker my_talker
[INFO] [1656050459.231579900] [my_listener]: receive: Hello, World!: cnt = 4
[INFO] [1656050460.231831200] [my_listener]: receive: Hello, World!: cnt = 5
[INFO] [1656050461.232120000] [my_listener]: receive: Hello, World!: cnt = 6
```
