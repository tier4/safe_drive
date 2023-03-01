# User Defined Data Structure

[Source code](https://github.com/tier4/safe_drive_tutorial/tree/main/msgtest).

Until previous tutorial, we used pre-defined message types.
In this tutorial, we will describe how to define user defined types.

## Create Project Directory

Then create a project directory as follows.

```text
$ mkdir -p msgtest/src
```

Throughout this tutorial, we will create 4 packages as follows.

| packages                     | description            |
|------------------------------|------------------------|
| msgtest/src/my_interfaces    | defining types of ROS2 |
| msgtest/src/talker           | a publisher            |
| msgtest/src/listener         | a subscriber           |

## Workspace's `Cargo.toml`

The workspace's `Cargo.toml` should be created as follows.

`msgtest/src/Cargo.toml`

```toml
[workspace]
members = ["talker", "listener"]
```

Then, create projects as follows.

```text
$ cd msgtest/src
$ cargo new talker
$ cargo new listener
```

## Define User Defined Type

To define message types, we have to create a ROS2's package,
and create a '.msg' files.
The package can be created in the ordinary way of ROS2 as follows.

```text
$ cd msgtest/src
$ ros2 pkg create --build-type ament_cmake my_interfaces
$ cd my_interfaces
$ mkdir msg
$ cd msg
```

### Primitive Type: `my_interfaces/msg/MyMsg.msg`

Then create a file, `msgtest/src/my_interfaces/msg`, as follows.

```text
int32 integer_value
int32[] unbounded_integer_array
int32[5] five_integers_array
int32[<=5] up_to_five_integers_array
```

There are 4 values in this type.

- `integer_value` : a value of the `int32` type
- `unbounded_integer_array` : an unbounded array of the `int32` type
- `five_integers_array` : an array which size is 5 of the `int32` type
- `up_to_five_integers_array` : an array whose size is up to 5 of the `int32` type

### Using User Defiend Type: `my_interfaces/msg/MyMsgs.msg`

We can use the `MyMsg` previously defined in another message type, `msgtest/src/my_interfaces/msg/MyMsgs.msg`, as follows.

```text
MyMsg msg1
MyMsg msg2
```

### String Type: `my_interfaces/msg/MyMsgStr.msg`

A size of an array can be specified as described above,
a length of a string can be also specified.
For example, `string<=10` is a type of string,
but its length is up to 10.

We prepare `msgtest/src/my_interfaces/msg/MyMsgStr.msg` as follows.

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

### Edit `my_interfaces/CMakeLists.txt`

To generate C or C++ files and libraries for used defined types,
we have to edit `CMakeLists.txt` as follows.

`msgtest/src/my_interfaces/CMakeLists.txt`

```cmake
find_package(rosidl_default_generators REQUIRED)

rosidl_generate_interfaces(${PROJECT_NAME}
  "msg/MyMsg.msg"
  "msg/MyMsgs.msg"
  "msg/MyMsgStr.msg"
)
```

We have to specify messages files in `CMakeLists.txt`.

### Edit `my_interfaces/package.xml`

We also have to edit `package.xml` as follows.


`msgtest/src/my_interfaces/package.xml`

```xml
<build_depend>rosidl_default_generators</build_depend>

<exec_depend>rosidl_default_runtime</exec_depend>

<member_of_group>rosidl_interface_packages</member_of_group>
```

## User Defined Type in Rust

Primitive types are translated into Rust's types as follows.

| ROS2    | Rust                       |
|---------|----------------------------|
| bool    | bool                       |
| byte    | u8                         |
| char    | i8                         |
| int8    | i8                         |
| uint8   | u8                         |
| int16   | i16                        |
| uint16  | u16                        |
| int32   | i32                        |
| uint32  | u32                        |
| int64   | i64                        |
| uint64  | u64                        |
| float32 | f32                        |
| float64 | f64                        |
| string  | safe_drive::msg::RosString |

### Generated Types

Array types are generated as follows.

| ROS2       | Rust                       |
|------------|----------------------------|
| int32[5]   | [i32; 5]                   |
| int32[]    | safe_drive::msg::I32Seq<0> |
| int32[<=5] | safe_drive::msg::I32Seq<5> |

`0` of `I32Seq<0>` indicates unbounded, and `5` of `I32Seq<5>` indicates less than or equal to 5.
So, `MyMsg` and `MyMsgs` are generated as follows.

## Talker

Let's implement a talker which publishes `MyMsgs` periodically.

### Edit `talker/Cargo.toml`

To use the generated types in Rust, we have to edit `Cargo.toml` as follows.
The most important thing is to add `my_interfaces`, which defines message types we use.

```toml
# msgtest/src/talker/Cargo.toml
[dependencies]
safe_drive = "0.2"
my_interfaces = { path = "/tmp/safe_drive_tutorial/msgtest/my_interfaces" }

[package.metadata.ros]
msg = ["my_interfaces"]
msg_dir = "/tmp/safe_drive_tutorial/msgtest"
safe_drive_version = "0.2"
```

### Create `talker/package.xml`

Then create `package.xml` as follows.

`msgtest/src/talker/package.xml`

```xml
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>talker</name>
  <version>0.0.0</version>
  <description>Talker in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>Apache License 2.0</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <depend>my_interfaces</depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

Don't forget `<depend>my_interfaces</depend>`.

### Generated Files

When you run `colcon`, it generate `my_interfaces` in Rust.

```text
$ cd msgtest
$ colcon build --cargo-args --release
```

Then, you can find Rust's files as follows.

`/tmp/safe_drive_tutorial/msgtest/my_interfaces/src/msg/my_msg.rs`

```rust
#[repr(C)]
#[derive(Debug)]
pub struct MyMsg {
    pub integer_value: i32,
    pub unbounded_integer_array: safe_drive::msg::I32Seq<0>,
    pub five_integers_array: [i32; 5],
    pub up_to_five_integers_array: safe_drive::msg::I32Seq<5>,
}
```

`/tmp/safe_drive_tutorial/msgtest/my_interfaces/src/msg/my_msgs.rs`

```rust
#[repr(C)]
#[derive(Debug)]
pub struct MyMsgs {
    pub msg1: crate::msg::my_msg::MyMsg,
    pub msg2: crate::msg::my_msg::MyMsg,
}
```

### Edit `talker/src/main.rs`

If you want to know how to implement a subscriber or a publisher, please see [a tutorial of Pub/Sub](./pubsub.md). This section describes how to handle a messages generated by `ros2msg_to_rs`.

`msgtest/src/talker/src/main.rs`

```rust
use safe_drive::{
    context::Context,
    error::DynError,
    logger::Logger,
    msg::{I32Seq, RosStringSeq},
    pr_info,
};
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

    my_msg.integer_value = 10;

    // int32[5] five_integers_array
    my_msg.five_integers_array[0] = 11;
    my_msg.five_integers_array[1] = 13;
    my_msg.five_integers_array[2] = 49;
    my_msg.five_integers_array[3] = 55;
    my_msg.five_integers_array[4] = 19;

    // int32[] unbounded_integer_array
    let mut msgs = I32Seq::new(3).unwrap();
    let ref_msgs = msgs.as_slice_mut();
    ref_msgs[0] = 6;
    ref_msgs[1] = 7;
    ref_msgs[2] = 8;
    my_msg.unbounded_integer_array = msgs;

    // int32[<=5] up_to_five_integers_array
    let mut msgs = I32Seq::new(2).unwrap();
    let ref_msgs = msgs.as_slice_mut();
    ref_msgs[0] = 2;
    ref_msgs[1] = 3;
    my_msg.up_to_five_integers_array = msgs;

    Ok(my_msg)
}
```

Primitive types and arrays can be handles in the ordinary way of Rust as follows.

```rust
my_msg.integer_value = 10;

// int32[5] five_integers_array
my_msg.five_integers_array[0] = 11;
my_msg.five_integers_array[1] = 13;
my_msg.five_integers_array[2] = 49;
my_msg.five_integers_array[3] = 55;
my_msg.five_integers_array[4] = 19;
```

To access elements of unbounded or bounded arrays,
we can use `as_slice_mut()` or `as_slice()` methods as follows.

```rust
// unbounded or unbounded array
let mut msgs = I32Seq::new(3).unwrap();
let ref_msgs = msgs.as_slice_mut();
```

`as_slice_mut()` returns a mutable slice,
you can thus update the elements of the array via the slice.

## Listener

Let's then implement a listener which receive messages published by the talker.

### Edit `listener/Cargo.toml`

The listener also requires `my_interfaces`, and edit `Cargo.toml` as follows.

```toml
# msgtest/src/listener/Cargo.toml
[dependencies]
safe_drive = "0.2"
my_interfaces = { path = "/tmp/safe_drive_tutorial/msgtest/my_interfaces" }

[package.metadata.ros]
msg = ["my_interfaces"]
msg_dir = "/tmp/safe_drive_tutorial/msgtest"
safe_drive_version = "0.2"
```

### Create `listener/package.xml`

Then create `package.xml` as follows.

`msgtest/src/listener/package.xml`

```xml
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>listener</name>
  <version>0.0.0</version>
  <description>Listener in Rust</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>Apache License 2.0</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <depend>my_interfaces</depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

Don't forget `<depend>my_interfaces</depend>`.

### Edit `listener/src/main.rs`

The listener can also be implemented straightforwardly as follows.

`msgtest/src/listener/src/main.rs`

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

            pr_info!(logger, "message: {}", msg.integer_value);

            for msg in msg.five_integers_array.iter() {
                pr_info!(logger, "five_integers_array: {}", msg);
            }

            for msg in msg.unbounded_integer_array.iter() {
                pr_info!(logger, "unbounded_integer_array: {}", msg);
            }

            for msg in msg.up_to_five_integers_array.iter() {
                pr_info!(logger, "up_to_five_integers_array: {}", msg);
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

## Compilation and Execution

Now, we can compile and execute the talker and listener. Let's do it!

### Compile

The compilation can be performed by using `colcon` as follows.

```text
$ cd msgtest
$ colcon build --cargo-args --release
$ . ./install/setup.bash
```

### Execute Listener

The listener can be executed by using `ros2` as follows.
After executing the talker, it receives messages as follows.

```text
$ ros2 run listener listener
[INFO] [1658305910.013449534] [listener]: listening
[INFO] [1658305914.359791460] [listener]: message: 10
[INFO] [1658305914.359839382] [listener]: five_integers_array: 11
[INFO] [1658305914.359867532] [listener]: five_integers_array: 13
[INFO] [1658305914.359880763] [listener]: five_integers_array: 49
[INFO] [1658305914.359889731] [listener]: five_integers_array: 55
[INFO] [1658305914.359900913] [listener]: five_integers_array: 19
[INFO] [1658305914.359912534] [listener]: unbounded_integer_array: 6
[INFO] [1658305914.359924084] [listener]: unbounded_integer_array: 7
[INFO] [1658305914.359936971] [listener]: unbounded_integer_array: 8
[INFO] [1658305914.359946479] [listener]: up_to_five_integers_array: 2
[INFO] [1658305914.359959422] [listener]: up_to_five_integers_array: 3
```

### Execute Talker

To execute the talker, open a new terminal window and execute it as follows.

```text
$ cd msgtest
$ . ./install/setup.bash
$ ros2 run talker talker
[INFO] [1658305913.359250753] [talker]: send: MyMsgs { msg1: MyMsg { integer_value: 10, unbounded_integer_array: I32Seq(rosidl_runtime_c__int32__Sequence { data: 0x55a0653f7aa0, size: 3, capacity: 3 }), five_integers_array: [11, 13, 49, 55, 19], up_to_five_integers_array: I32Seq(rosidl_runtime_c__int32__Sequence { data: 0x55a0653efaa0, size: 2, capacity: 2 }) }, msg2: MyMsg { integer_value: 10, unbounded_integer_array: I32Seq(rosidl_runtime_c__int32__Sequence { data: 0x55a0653f7e30, size: 3, capacity: 3 }), five_integers_array: [11, 13, 49, 55, 19], up_to_five_integers_array: I32Seq(rosidl_runtime_c__int32__Sequence { data: 0x55a0653f7e50, size: 2, capacity: 2 }) }
```

Nicely done! Now, we can define new types and handle the types in Rust.

## String Type

Arrays of string are bit different from arrays of primitive types.
`string` is unbounded string, and `string<=5` is bounded string whose length is up to 5.
So, there are arrays for unbounded and bounded strings as follows; `msg` is `safe_drive::msg`.

| ROS             | Rust                    |
|-----------------|-------------------------|
| string          | msg::RosString<0>       |
| string[]        | msg::StringSeq<0, 0>    |
| string[<=5]     | msg::StringSeq<0, 5>    |
| string[10]      | [msg::RosString<0>; 10] |
| string<=5       | msg::RosString<5>       |
| string<=5[<=10] | msg::StringSeq<5, 10>   |
| string<=5[10]   | [msg::RosString<5>; 10] |

`RosString<0>` is a type of unbounded string, and `RosString<5>` is a type of bounded string whose length is less than or equal to 5.
`5` of `StringSeq<5, 10>` indicates the length of a string is less than or equal to 5,
and `10` of it indicates the length of the array is less than or equal to 10.

For example, the following ROS2 message type can be translated into the `MyMsgStr` as follows.

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

`/tmp/safe_drive_tutorial/msgtest/my_interfaces/src/msg/my_msg_str.rs`

```rust
#[repr(C)]
#[derive(Debug)]
pub struct MyMsgStr {
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

To access to elements of string arrays,
we can use `as_slice_mut()` or `as_slice_mut()` as follows.

```rust
fn _create_message_str() -> Result<my_interfaces::msg::MyMsgStr, DynError> {
    let mut my_msg = my_interfaces::msg::MyMsgStr::new().unwrap();

    // string message
    my_msg.message.assign("Hello, World!");

    // string[2] static_array_str
    my_msg.static_array_str[0].assign("static array 0");
    my_msg.static_array_str[1].assign("static array 1");

    // string[] dynamic_array_str
    let mut msgs = RosStringSeq::new(3).ok_or("failed to create string")?;
    let ref_msgs = msgs.as_slice_mut();
    ref_msgs[0].assign("dynamic array 0");
    ref_msgs[1].assign("dynamic array 1");
    ref_msgs[2].assign("dynamic array 2");
    my_msg.dynamic_array_str = msgs;

    // string[<=3] bounded_array_str
    let mut msgs = RosStringSeq::new(2).ok_or("failed to create string")?;
    let ref_msgs = msgs.as_slice_mut();
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
    let ref_msgs = msgs.as_slice_mut();
    ref_msgs[0].assign("msg3");
    ref_msgs[1].assign("msg4");
    ref_msgs[2].assign("msg5");
    my_msg.dynamic_array_bounded_str = msgs;

    // string<=10[<=3] bounded_array_bounded_str
    let mut msgs = RosStringSeq::new(2).ok_or("failed to create string")?;
    let ref_msgs = msgs.as_slice_mut();
    ref_msgs[0].assign("msg3");
    ref_msgs[1].assign("msg5");
    my_msg.bounded_array_bounded_str = msgs;

    Ok(my_msg)
}
```
