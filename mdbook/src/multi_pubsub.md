# Multi-threaded Publish and Subscribe

[Source code](https://github.com/tier4/safe_drive_tutorial/tree/main/mt_pubsub).

Previous chapters use a selector to wait messages.
A selector can be used by only a single thread.
This means previous implementation is single-threaded.

To execute tasks concurrently, we can use the async/await feature of Rust.
By using this, we can implement multi-threaded applications.
In this chapter, we will describe how to use `safe_drive` with async/await.
We use `async_std` as a asynchronous library,
but you can use `Tokio` instead.

## Creating Projects

Before implementing, we need to prepare projects as follows.

```text
$ mkdir -p mt_pubsub/src
$ cd mt_pubsub/src
$ cargo new publishers
$ cargo new subscribers
```

The `mt_pubsub` is the root directory of this project,
and we created `publishers` and `subscribers` of Rust's projects.
At the moment, the following directories is present.

| Directories               | What?               |
|---------------------------|---------------------|
| mt_pubsub/src/publishers  | publishers in Rust  |
| mt_pubsub/src/subscribers | subscribers in Rust |

## Common Configuration

Then, we have to create or edit the following files for basic configurations.

| Files                                 | What?                 |
|---------------------------------------|-----------------------|
| mt_pubsub/src/publishers/Cargo.toml   | for Cargo             |
| mt_pubsub/src/publishers/package.xml  | for ROS2              |
| mt_pubsub/src/publishers/build.rs     | for rustc             |
| mt_pubsub/src/subscribers/Cargo.toml  | for Cargo             |
| mt_pubsub/src/subscribers/package.xml | for ROS2              |
| mt_pubsub/src/subscribers/build.rs    | for rustc             |
| mt_pubsub/src/Cargo.toml              | for Cargo's workspace |

To enable rust-analyzer in the `mt_pubsub` directory and reduce the compilation time,
prepare workspace's `Cargo.toml` as follows.

`mt_pubsub/src/Cargo.toml`

```toml
[workspace]
members = ["publishers", "subscribers"]
```

`package.xml`s are almost same as [Publish and Subscribe](./pubsub.md).
If you cannot understand what these files do,
please go back to the previous chapter.

`publishers/package.xml`

```xml
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>publishers</name>
  <version>0.0.0</version>
  <description>MT-Publishers</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>Apache License 2.0</license>

  <depend>std_msgs</depend>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

`subscribers/package.xml`

```xml
  <name>subscribers</name>
  <description>MT-Subscribers</description>
```

To use `async_std`, we have to update `Cargo.toml` as follows.

`Cargo.toml`

```toml
[dependencies]
async-std = { version = "1", features = ["attributes"] }
safe_drive = "0.2"
std_msgs = { path = "/tmp/safe_drive_tutorial/mt_pubsub/std_msgs" }

[package.metadata.ros]
msg = ["std_msgs"]
msg_dir = "/tmp/safe_drive_tutorial/mt_pubsub"
safe_drive_version = "0.2"
```

## Publishers

The `publishers` publishes messages to 2 topics periodically.
This create 2 tasks.
One is send a message every 500ms,
and another is send a message every 250ms.
The code of the `publishers` is as follows.

`mt_pubsub/src/publishers/src/main.rs`

```rust
use safe_drive::{context::Context, error::DynError};
use std::time::Duration;

#[async_std::main]
async fn main() -> Result<(), DynError> {
    // Create a context and a node.
    let ctx = Context::new()?;
    let node = ctx.create_node("publishers", None, Default::default())?;

    // Create publishers.
    let publisher1 = node.create_publisher::<std_msgs::msg::String>("topic1", None)?;
    let publisher2 = node.create_publisher::<std_msgs::msg::String>("topic2", None)?;

    // Create a task which sends "Hello, World!".
    let task1 = async_std::task::spawn(async move {
        let mut msg = std_msgs::msg::String::new().unwrap();
        msg.data.assign("Hello, World!");
        for _ in 0..50 {
            publisher1.send(&msg).unwrap(); // Send a message.
            async_std::task::sleep(Duration::from_millis(500)).await; // Sleep 500ms.
        }
    });

    // Create a task which sends "Hello, Universe!".
    let task2 = async_std::task::spawn(async move {
        let mut msg = std_msgs::msg::String::new().unwrap();
        msg.data.assign("Hello, Universe!");
        for _ in 0..100 {
            publisher2.send(&msg).unwrap(); // Send a message.
            async_std::task::sleep(Duration::from_millis(250)).await; // Sleep 250ms.
        }
    });

    task1.await;
    task2.await;

    Ok(())
}
```

The `async_std::task::spawn` creates a asynchronous task,
which is similar to a thread.
The following is a excerpt creating a task which sends "Hello, World!"
to "topic1" every 500ms.

```rust
// Create a task which sends "Hello, World!".
let task1 = async_std::task::spawn(async move {
    let mut msg = std_msgs::msg::String::new().unwrap();
    msg.data.assign("Hello, World!");
    for _ in 0..50 {
        publisher1.send(&msg).unwrap(); // Send a message.
        async_std::task::sleep(Duration::from_millis(500)).await; // Sleep 500ms.
    }
});
```

This excerpt sends a message by `Publisher::send` and sleep by `async_std::task::sleep`.
Note that this uses `async_std::task::sleep` instead of `std::thread::sleep`,
because the former is non-blocking but the the latter is blocking.
Calling blocking functions should be avoided in asynchronous tasks.

## Subscribers

Then, let's implement the `subscribers`.
The main function is almost same as previous one.

`mt_pubsub/src/subscribers/src/main`

```rust
use safe_drive::{
    context::Context, error::DynError, logger::Logger, pr_info, topic::subscriber::Subscriber,
};

#[async_std::main]
async fn main() -> Result<(), DynError> {
    // Create a context and a node.
    let ctx = Context::new()?;
    let node = ctx.create_node("subscribers", None, Default::default())?;

    // Create subscribers.
    let subscriber1 = node.create_subscriber::<std_msgs::msg::String>("topic1", None)?;
    let subscriber2 = node.create_subscriber::<std_msgs::msg::String>("topic2", None)?;

    // Receive messages.
    let task1 = async_std::task::spawn(receiver(subscriber1));
    let task2 = async_std::task::spawn(receiver(subscriber2));

    task1.await?;
    task2.await?;

    Ok(())
}

async fn receiver(mut subscriber: Subscriber<std_msgs::msg::String>) -> Result<(), DynError> {
    let logger = Logger::new(subscriber.get_topic_name());

    loop {
        // Receive a message
        let msg = subscriber.recv().await?;
        pr_info!(logger, "{}", msg.data);
    }
}
```

`Subscriber::recv` is an asynchronous function to receive a message.
To receive asynchronously, use the `.await` keyword.
If there is a message to be received, `recv().await` returns the message immediately.
Otherwise, it yields the execution to another task and sleeps until arriving a message.

### Modification for Timeout

By using a timeout mechanism provided by asynchronous libraries,
we can implement receiving with timeout.
Timeout can be implemented as follows.

```rust
use async_std::future::timeout;
use safe_drive::pr_warn;
use std::time::Duration;
async fn receiver(mut subscriber: Subscriber<std_msgs::msg::String>) -> Result<(), DynError> {
    let logger = Logger::new(subscriber.get_topic_name());

    loop {
        // Receive a message with 3s timeout.
        match timeout(Duration::from_secs(3), subscriber.recv()).await {
            Ok(result) => pr_info!(logger, "received: {}", result?.data),
            Err(_) => {
                // Timed out. Finish receiving.
                pr_warn!(logger, "timeout");
                break;
            }
        }
    }

    Ok(())
}
```

`async_std::timeout` is a function to represent timeout.
`timeout(Duration::from_secs(3), subscriber.recv()).await` calls `subscriber.recv()` asynchronously,
but it will be timed out after 3s later.

## Execution

First, execute `publishers` in a terminal application window as follows.

```text
$ cd mt_pubsub
$ colcon build --cargo-args --release
$ . ./install/setup.bash
$ ros2 run publishers publishers
```

Then, execute `subscribers` in another terminal application window as follows.
This uses timeout for receiving.

```text
$ cd mt_pubsub.
$ . ./install/setup.bash
$ ros2 run subscribers subscribers
[INFO] [1657076046.969809600] [topic2]: received: Hello, Universe!
[INFO] [1657076047.220104100] [topic2]: received: Hello, Universe!
[INFO] [1657076047.447426100] [topic1]: received: Hello, World!
[INFO] [1657076047.470348600] [topic2]: received: Hello, Universe!
[INFO] [1657076047.721980900] [topic2]: received: Hello, Universe!
[WARN] [1657076050.448393200] [topic1]: timeout
[WARN] [1657076050.722433800] [topic2]: timeout
```

Nicely done!
We are sending and receiving messages asynchronously.
In addition to that, the timeouts work correctly.
