# Multi-threaded Publish and Subscribe

##

```text
$ mkdir -p mt_pubsub/src
$ cd mt_pubsub/src
$ cargo new publishers
$ cargo new subscribers
```

| Directories               | What?               |
|---------------------------|---------------------|
| mt_pubsub/src/publishers  | publishers in Rust  |
| mt_pubsub/src/subscribers | subscribers in Rust |
| mt_pubsub/install         | created by colcon   |

## Common Configuration

| Files                                 | What?     |
|---------------------------------------|-----------|
| mt_pubsub/src/publishers/Cargo.toml   | for Cargo |
| mt_pubsub/src/publishers/package.xml  | for ROS2  |
| mt_pubsub/src/publishers/build.rs     | for rustc |
| mt_pubsub/src/publishers/src/main.rs  | main      |
| mt_pubsub/src/subscribers/Cargo.toml  | for Cargo |
| mt_pubsub/src/subscribers/package.xml | for ROS2  |
| mt_pubsub/src/subscribers/build.rs    | for rustc |
| mt_pubsub/src/subscribers/src/main    | main      |

```rust
// build.rs
fn main() {
    if let Some(e) = std::env::var_os("AMENT_PREFIX_PATH") {
        let env = e.to_str().unwrap();
        for path in env.split(":") {
            println!("cargo:rustc-link-search={path}/lib");
        }
    }
}
```

```toml
# Cargo.toml
[dependencies]
async-std = { version = "1.12.0", features = ["attributes"] }
safe_drive = { path = "../../../safe_drive" }
```

```xml
<!-- package.xml -->
<?xml version="1.0"?>
<?xml-model href="http://download.ros.org/schema/package_format3.xsd" schematypens="http://www.w3.org/2001/XMLSchema"?>
<package format="3">
  <name>publishers</name>
  <version>0.0.0</version>
  <description>MT-Publishers</description>
  <maintainer email="yuuki.takano@tier4.jp">Yuuki Takano</maintainer>
  <license>TODO: License declaration</license>

  <test_depend>ament_lint_auto</test_depend>
  <test_depend>ament_lint_common</test_depend>

  <export>
    <build_type>ament_cargo</build_type>
  </export>
</package>
```

```xml
  <name>subscribers</name>
  <description>MT-Subscribers</description>
```

## Publishers

```rust
use safe_drive::{context::Context, error::DynError, msg::common_interfaces::std_msgs};
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

## Subscribers

```rust
use async_std::future::timeout;
use safe_drive::{
    context::Context, error::DynError, logger::Logger, msg::common_interfaces::std_msgs, pr_info,
    pr_warn, topic::subscriber::Subscriber,
};
use std::time::Duration;

#[async_std::main]
async fn main() -> Result<(), DynError> {
    // Create a context and a node.
    let ctx = Context::new()?;
    let node = ctx.create_node("subscribers", None, Default::default())?;

    // Create subsucribers.
    let subscriber1 = node.create_subscriber::<std_msgs::msg::String>("topic1", None)?;
    let subscriber2 = node.create_subscriber::<std_msgs::msg::String>("topic2", None)?;

    // Receive messages.
    let task1 = async_std::task::spawn(async move { receiver(subscriber1).await });
    let task2 = async_std::task::spawn(async move { receiver(subscriber2).await });

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

```rust
async fn receiver(
    mut subscriber: Subscriber<std_msgs::msg::String>,
) -> Result<(), DynError> {
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

## Execution

```text
$ cd mt_pubsub
$ colcon build --cargo-args --release
$ . ./install/setup.bash
$ ros2 run publishers publishers
```

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
