# Timer

```text
$ export LIBRARY_PATH=/opt/ros/galactic/lib:$LIBRARY_PATH
```

## Wall-timer

```text
$ cargo new wall_timer
$ cd wall_timer
```

```toml
[dependencies]
safe_drive = { path = "../safe_drive" }
```

```rust
use safe_drive::{
    context::Context, error::DynError, logger::Logger, msg::common_interfaces::std_msgs, pr_info,
};
use std::{rc::Rc, time::Duration};

fn main() -> Result<(), DynError> {
    // Create a context, a node, a subscriber, a publisher, and a selector.
    let ctx = Context::new()?;
    let node = ctx.create_node("my_node", None, Default::default())?;
    let subscriber = node.create_subscriber::<std_msgs::msg::UInt64>("my_topic", None)?;
    let publisher = node.create_publisher::<std_msgs::msg::UInt64>("my_topic", None)?;
    let mut selector = ctx.create_selector()?;

    // Create a logger.
    // To share this by multiple callback functions, use Rc.
    let logger = Rc::new(Logger::new("wall timer example"));

    // Add a wall timer to publish periodically.
    let mut cnt = Box::new(0);
    let mut msg = std_msgs::msg::UInt64::new().unwrap();
    let logger1 = logger.clone();

    selector.add_wall_timer(
        "publisher", // the name of timer
        Duration::from_secs(1),
        Box::new(move || {
            msg.data = *cnt;
            *cnt += 1;
            publisher.send(&msg).unwrap();
            pr_info!(logger1, "send: msg.data = {}", msg.data);
        }),
    );

    // Add a subscriber.
    selector.add_subscriber(
        subscriber,
        Box::new(move |msg| {
            pr_info!(logger, "received: msg.data = {}", msg.data);
        }),
        false,
    );

    // Spin.
    loop {
        selector.wait()?;
    }
}
```

```text
$ cargo run
[INFO] [1656557242.842509800] [wall timer example]: send: msg.data = 0
[INFO] [1656557242.842953300] [wall timer example]: received: msg.data = 0
[INFO] [1656557243.843103800] [wall timer example]: send: msg.data = 1
[INFO] [1656557243.843272900] [wall timer example]: received: msg.data = 1
[INFO] [1656557244.843574600] [wall timer example]: send: msg.data = 2
[INFO] [1656557244.844021200] [wall timer example]: received: msg.data = 2
[INFO] [1656557245.844349800] [wall timer example]: send: msg.data = 3
[INFO] [1656557245.844702900] [wall timer example]: received: msg.data = 3
```

## One-shot Timer

```rust
use safe_drive::{context::Context, error::DynError, logger::Logger, pr_info};
use std::time::Duration;

fn main() -> Result<(), DynError> {
    // Create a context, a publisher, and a logger.
    let ctx = Context::new()?;
    let mut selector = ctx.create_selector()?;
    let logger = Logger::new("one-shot timer example");

    // Add a one-shot timer.
    selector.add_timer(
        Duration::from_secs(2),
        Box::new(move || pr_info!(logger, "fired!")),
    );

    // Wait the timer.
    selector.wait()?;

    Ok(())
}
```
