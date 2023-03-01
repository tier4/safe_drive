# Timer

[Source code](https://github.com/tier4/safe_drive_tutorial/tree/main/timers).

This tutorial does not use `colcon` to build.
We use only `cargo`, which is a Rust's standard build system.

Don't forget loading ROS2's environment as follows.
If you already done so, you do not need this.

```text
$ . /opt/ros/humble/setup.bash
```

## Wall-timer

A wall-timer is a timer which periodically invoked.
This section describes how to use a wall-timer.

Let's create a package by using a `cargo` as follows.

```text
$ cargo new wall_timer
$ cd wall_timer
```

Then, add `safe_drive` to the dependencies of `Cargo.toml`.

```toml
[dependencies]
safe_drive = "0.2"
```

The following code is an example using a wall-timer.
The important method is `Selector::add_wall_timer()` which takes
a name, a duration, and a callback function.

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
    );

    // Spin.
    loop {
        selector.wait()?;
    }
}
```

Timers can be set by a method of selector as follows,
and the timers will be invoked when calling the `Selector::wait()` methods.

```rust
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
```

- `"publisher"` is the name of this timer. The name is used for statistics. You can use any name.
- `Duration::from_secs(1)` is the duration for periodic invoking. This argument means the callback function is invoked every 1 second.
- `Box::new(move || ...)` is the callback function.

There is a publisher invoked by a timer, and a subscriber in this code.
When executing this, transmission and reception will be confirmed as follows.

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

A wall-timer is invoked periodically,
but one-shot timer is invoked only once.
A one-shot can be set by the `Selector::add_timer()` method as follows.

```rust
use safe_drive::{context::Context, error::DynError, logger::Logger, pr_info};
use std::{cell::RefCell, collections::VecDeque, rc::Rc, time::Duration};

pub fn main() -> Result<(), DynError> {
    // Create a context, a publisher, and a logger.
    let ctx = Context::new()?;
    let mut selector = ctx.create_selector()?;
    let logger = Rc::new(Logger::new("one-shot timer example"));

    let queue = Rc::new(RefCell::new(VecDeque::new()));

    // Add a one-shot timer.
    let queue1 = queue.clone();
    selector.add_timer(
        Duration::from_secs(2),
        Box::new(move || {
            pr_info!(logger, "fired!");

            // Insert a timer to the queue.
            let mut q = queue1.borrow_mut();
            let logger1 = logger.clone();
            q.push_back((
                Duration::from_secs(2),
                (Box::new(move || pr_info!(logger1, "fired! again!"))),
            ));
        }),
    );

    // Spin.
    loop {
        {
            // Set timers.
            let mut q = queue.borrow_mut();
            while let Some((dur, f)) = q.pop_front() {
                selector.add_timer(dur, f);
            }
        }

        selector.wait()?;
    }
}
```

`Selector::add_timer()` does not take the name,
but other arguments are same as `Selector::add_wall_timer()`.

```rust
selector.add_timer(
    Duration::from_secs(2),
    Box::new(move || ...),
);
```

- `Duration::from_secs(2)` is a duration indicating when the timer will be invoked.
- `Box::new(move || ...)` is the callback function.

This code reenables a timer in the callback function.
To reenable, the callback takes a `queue` and
timers in the `queue` is reenabled in the spin as follows.

```rust
// Spin.
loop {
    {
        // Set timers.
        let mut q = queue.borrow_mut();
        while let Some((dur, f)) = q.pop_front() {
            selector.add_timer(dur, f);
        }
    }

    selector.wait()?;
}
```

The important thing is that the borrowed resources must be released.
To release definitely, the code fraction borrowing the `queue` is surrounded by braces.

The following is a execution result of this code.

```
$ cargo run
[INFO] [1657070943.324438900] [one-shot timer example]: fired!
[INFO] [1657070945.324675600] [one-shot timer example]: fired! again!
```
