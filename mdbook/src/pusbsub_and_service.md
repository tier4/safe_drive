# Request to Server in Callback

[Source code](https://github.com/tier4/safe_drive_tutorial/tree/main/pubsubsrv).

In this chapter, we will introduce how to access a server in a callback function.
The code introduced here can be implemented by using async/await more beautifully.

## Subscriber and Client

The concept here is very simple.
We use 2 selectors for a callback function and accessing a server,
and `recv_timeout()` to receive a response from the server.

We only show Rust code of a publisher as follows.
Other files can be found in [Source code](https://github.com/tier4/safe_drive_tutorial/tree/main/pubsubsrv).

```rust
use safe_drive::{
    context::Context,
    error::DynError,
    logger::Logger,
    msg::common_interfaces::{std_msgs, std_srvs},
    pr_fatal, pr_info,
    selector::Selector,
    service::client::Client,
    topic::subscriber::Subscriber,
    RecvResult,
};
use std::time::Duration;

fn main() -> Result<(), DynError> {
    // Create a context and a node.
    let ctx = Context::new()?;
    let node = ctx.create_node("listen_client", None, Default::default())?;

    // Create 2 selectors.
    let selector = ctx.create_selector()?;
    let selector_client = ctx.create_selector()?;

    // Create a subscriber, a client, and a logger.
    let subscriber = node.create_subscriber::<std_msgs::msg::Empty>("pubsubsrv_topic", None, true)?;
    let client = node.create_client::<std_srvs::srv::Empty>("pubsubsrv_service", None, true)?;

    worker(selector, selector_client, subscriber, client)?;

    Ok(())
}

fn worker(
    mut selector: Selector,
    mut selector_client: Selector,
    subscriber: Subscriber<std_msgs::msg::Empty>,
    client: Client<std_srvs::srv::Empty>,
) -> Result<(), DynError> {
    let mut client = Some(client);
    let logger = Logger::new("listen_client");

    selector.add_subscriber(
        subscriber,
        Box::new(move |_msg| {
            pr_info!(logger, "receive a message");

            // Take the client.
            let c = client.take().unwrap();

            let request = std_srvs::srv::EmptyRequest::new().unwrap();

            // Send a request.
            let receiver = c.send(&request).unwrap();

            // Receive a response.
            match receiver.recv_timeout(Duration::from_millis(20), &mut selector_client) {
                RecvResult::Ok((c, _response, _header)) => {
                    pr_info!(logger, "receive a response");
                    client = Some(c)
                }
                RecvResult::RetryLater(r) => client = Some(r.give_up()),
                RecvResult::Err(e) => {
                    pr_fatal!(logger, "{e}");
                    panic!()
                }
            }
        }),
    );

    loop {
        selector.wait()?;
    }
}
```

## in Detail

The important pieces are as follows.
This code create 2 selectors first.
`selector_client` is used for a service.

```rust
// Create 2 selectors.
let selector = ctx.create_selector()?;
let selector_client = ctx.create_selector()?;
```

In the callback function, `recv_timeout()` method, which takes
`selector_client`, is used as follows.

```rust
// Send a request.
let receiver = c.send(&request).unwrap();

// Receive a response.
match receiver.recv_timeout(Duration::from_millis(20), &mut selector_client) {
    RecvResult::Ok((c, _response, _header)) => {
        pr_info!(logger, "receive a response");
        client = Some(c)
    }
    RecvResult::RetryLater(r) => client = Some(r.give_up()),
    RecvResult::Err(e) => {
        pr_fatal!(logger, "{e}");
        panic!()
    }
}
```

In this callback function,
it sends a request to the server and receives a response
by `recv_timeout()` method.

## State Change

A service's state can be represented as follows.

 ```mermaid
graph LR;
    Start-->Send
    Send-->Receive
    Receive-->Send
```

To represent the state, `safe_drive` uses the type system of Rust.

First, a client is created as follows.
At that time, it must be `Send` state.

```rust
let mut client = Some(client); // Send state.
```

`send()` method consumes the client and returns
`receiver`.
It means the state is changed from Send to Receive.

```rust
let c = client.take().unwrap();
let receiver = c.send(&request).unwrap(); // Change state from Send to Receive.
```

`recv_timeout()` also consumes `receiver` and returns a new client
to send a new request if it successfully receives a response.

```rust
// Receive a response.
match receiver.recv_timeout(Duration::from_millis(20), &mut selector_client) {
    RecvResult::Ok((c, _response, _header)) => {
        pr_info!(logger, "receive a response");
        client = Some(c)
    }
    RecvResult::RetryLater(r) => client = Some(r.give_up()),
    RecvResult::Err(e) => {
        pr_fatal!(logger, "{e}");
        panic!()
    }
}
```

When it has timed out, you can choose retrying or giving up.
This code chooses giving up by `give_up()` method.
`give_up()` methods consumes a receiver and return a new
client to send a new request.

This code will work, but we think using async/await is better than this because it is designed for asynchronous programming.
I recommend to rewrite this code by using async/await.
