# User Defined Data Structure

## Installing `ros2msg_to_rs`

```text
$ git clone https://github.com/tier4/ros2msg_to_rs.git
$ cd ros2msg_to_rs
$ cargo build --release
$ cargo instal --path .
```

```text
$ mkdir -p msgtest/src
```

## Defining User Defined Type

```text
$ cd msgtest/src
$ ros2 pkg create --build-type ament_cmake my_interfaces
$ cd my_interfaces
$ mkdir msg
$ cd msg
```

`msgtest/src/my_interfaces/msg`

`msgtest/src/my_interfaces/msg/MyMsg.msg`

```text
string message
string[2] static_array_str
string[] dynamic_array_str
string[<=3] bounded_array_str

string<=10 bounded_str
string<=10[2] static_array_bounded_str
string<=10[] dynamic_array_bounded_str
string<=10[<=3] bounded_array_bounded_str
```

`msgtest/src/my_interfaces/msg/MyMsgs.msg`

```text
MyMsg msg1
MyMsg msg2
```


```text
$ cd msgtest/src
$ cargo new --lib my_interfaces_rs
$ ros2msg_to_rs -o my_interfaces_rs/src -i my_interfaces
$ generating: my_interfaces_rs/src/msg/msg/my_msg.rs
$ generating: my_interfaces_rs/src/msg/msg.rs
$ generating: my_interfaces_rs/src/mod.rs
$ generating: my_interfaces_rs/src/msg/mod.rs
```

```cmake
# msgtest/src/my_interfaces/CMakeLists.txt
find_package(rosidl_default_generators REQUIRED)

rosidl_generate_interfaces(${PROJECT_NAME}
  "msg/MyMsg.msg"
)
```

```xml
<!-- msgtest/src/my_interfaces/package.xml -->
<build_depend>rosidl_default_generators</build_depend>

<exec_depend>rosidl_default_runtime</exec_depend>

<member_of_group>rosidl_interface_packages</member_of_group>
```

## User Defined Type in Rust

```text
$ cd msgtest/src
$ create new --lib my_interfaces_rs
$ ros2msg_to_rs  -i ./ -o ./my_interfaces_rs/src
```

```rust
// msgtest/src/my_interfaces_rs/src/my_interfaces/msg/my_msg.rs
#[repr(C)]
#[derive(Debug)]
pub struct MyMsg {
    pub message: safe_drive::msg::RosString<0>,
    pub static_array_str: [safe_drive::msg::RosString<0>; 2],
    pub dynamic_array_str: safe_drive::msg::RosStringSeq<0, 0>,
    pub bounded_array_str: safe_drive::msg::RosStringSeq<0, 3>,
    pub bounded_str: safe_drive::msg::RosString<10>,
    pub static_array_bounded_str: [safe_drive::msg::RosString<10>; 2],
    pub dynamic_array_bounded_str: safe_drive::msg::RosStringSeq<10, 0>,
    pub bounded_array_bounded_str: safe_drive::msg::RosStringSeq<10, 3>,
}
```

```rust
// msgtest/src/my_interfaces_rs/src/my_interfaces/msg/my_msgs.rs
#[repr(C)]
#[derive(Debug)]
pub struct MyMsgs {
    pub msg1: MyMsg,
    pub msg2: MyMsg,
}
```

```rust
// msgtest/src/my_interfaces_rs/src/lib.rs
#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(unused_imports)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::too_many_arguments)]

pub mod my_interfaces;
```

```xml
<!-- msgtest/src/my_interfaces_rs/package.xml -->
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>my_interfaces_rs</name>
  <version>0.0.0</version>
  <description>My Interfaces in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

```rust
// msgtest/src/my_interfaces_rs/build.rs
fn main() {
    println!("cargo:rustc-link-lib=my_interfaces__rosidl_generator_c");
    println!("cargo:rustc-link-lib=my_interfaces__rosidl_typesupport_c");

    if let Some(e) = std::env::var_os("AMENT_PREFIX_PATH") {
        let env = e.to_str().unwrap();
        for path in env.split(':') {
            println!("cargo:rustc-link-search={path}/lib");
        }
    }
}
```

## Talker

```rust
use my_interfaces_rs::my_interfaces;
use safe_drive::{context::Context, error::DynError, logger::Logger, msg::RosStringSeq, pr_info};
use std::time::Duration;

fn main() -> Result<(), DynError> {
    // Create a context.
    let ctx = Context::new()?;

    // Create a node.
    let node = ctx.create_node("talker", None, Default::default())?;

    // Create a publisher.
    let publisher = node.create_publisher::<my_interfaces::msg::MyMsgs>("my_topic", None)?;

    // Create a logger.
    let logger = Logger::new("talker");

    // Create a message
    let my_msg1 = create_message()?;
    let my_msg2 = create_message()?;

    let mut my_msgs = my_interfaces::msg::MyMsgs::new().ok_or("failed to create MyMsgs")?;
    my_msgs.msg1 = my_msg1;
    my_msgs.msg2 = my_msg2;

    loop {
        pr_info!(logger, "send: {:?}", my_msgs); // Print log.

        // Send a message.
        publisher.send(&my_msgs)?;

        std::thread::sleep(Duration::from_secs(1));
    }
}

fn create_message() -> Result<my_interfaces::msg::MyMsg, DynError> {
    let mut my_msg = my_interfaces::msg::MyMsg::new().unwrap();

    // string message
    my_msg.message.assign("Hello, World!");

    // string[2] static_array_str
    my_msg.static_array_str[0].assign("static array 0");
    my_msg.static_array_str[1].assign("static array 1");

    // string[] dynamic_array_str
    let mut msgs = RosStringSeq::new(3).ok_or("failed to create string")?;
    let ref_msgs = msgs.as_slice_mut().ok_or("failed to get slice")?;
    ref_msgs[0].assign("dynamic array 0");
    ref_msgs[1].assign("dynamic array 1");
    ref_msgs[2].assign("dynamic array 2");
    my_msg.dynamic_array_str = msgs;

    // string[<=3] bounded_array_str
    let mut msgs = RosStringSeq::new(2).ok_or("failed to create string")?;
    let ref_msgs = msgs.as_slice_mut().ok_or("failed to get slice")?;
    ref_msgs[0].assign("bounded array 0");
    ref_msgs[1].assign("bounded array 1");
    my_msg.bounded_array_str = msgs;

    // string<=10 bounded_str
    my_msg.bounded_str.assign("Hello!");

    // string<=10[2] static_array_bounded_str
    my_msg.static_array_bounded_str[0].assign("msg1");
    my_msg.static_array_bounded_str[1].assign("msg2");

    // string<=10[] dynamic_array_bounded_str
    let mut msgs = RosStringSeq::new(3).ok_or("failed to create string")?;
    let ref_msgs = msgs.as_slice_mut().ok_or("failed to get slice")?;
    ref_msgs[0].assign("msg3");
    ref_msgs[1].assign("msg4");
    ref_msgs[2].assign("msg5");
    my_msg.dynamic_array_bounded_str = msgs;

    // string<=10[<=3] bounded_array_bounded_str
    let mut msgs = RosStringSeq::new(2).ok_or("failed to create string")?;
    let ref_msgs = msgs.as_slice_mut().ok_or("failed to get slice")?;
    ref_msgs[0].assign("msg3");
    ref_msgs[1].assign("msg5");
    my_msg.bounded_array_bounded_str = msgs;

    Ok(my_msg)
}
```

```toml
[dependencies]
safe_drive = { path = "/root/safe_drive" }
my_interfaces_rs = { path = "../my_interfaces_rs" }
```

```xml
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>talker</name>
  <version>0.0.0</version>
  <description>Talker in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <depend>my_interfaces</depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

## Listener

```rust
use my_interfaces_rs::my_interfaces;
use safe_drive::{context::Context, error::DynError, logger::Logger, pr_info};

fn main() -> Result<(), DynError> {
    // Create a context.
    let ctx = Context::new()?;

    // Create a node.
    let node = ctx.create_node("listener", None, Default::default())?;

    // Create a subscriber.
    let subscriber = node.create_subscriber::<my_interfaces::msg::MyMsgs>("my_topic", None)?;

    // Create a logger.
    let logger = Logger::new("listener");

    // Create a selector.
    let mut selector = ctx.create_selector()?;

    pr_info!(logger, "listening");

    // Add a callback function.
    selector.add_subscriber(
        subscriber,
        Box::new(move |msg| {
            let msg = &msg.msg1;

            pr_info!(logger, "message: {}", msg.message);

            for msg in msg.static_array_str.iter() {
                pr_info!(logger, "static_array_str: {}", msg);
            }

            if let Some(slice) = msg.dynamic_array_str.as_slice() {
                for msg in slice {
                    pr_info!(logger, "dynamic_array_str: {}", msg);
                }
            }
        }),
        false,
    );

    // Spin.
    loop {
        selector.wait()?;
    }
}
```

```toml
[dependencies]
safe_drive = { path = "/root/safe_drive" }
my_interfaces_rs = { path = "../my_interfaces_rs" }
```

```xml
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>listener</name>
  <version>0.0.0</version>
  <description>Listener in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <depend>my_interfaces</depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```
