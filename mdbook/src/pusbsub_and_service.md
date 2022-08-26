# Using Both Topic and Service with Callback Based Execution

## Subscriber and Client

```rust
use safe_drive::{
    context::Context,
    error::DynError,
    logger::Logger,
    msg::common_interfaces::{std_msgs, std_srvs},
    pr_error, pr_fatal,
    selector::Selector,
    service::client::Client,
    topic::subscriber::Subscriber,
    RecvResult, ST,
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
    let subscriber = node.create_subscriber::<std_msgs::msg::Empty>("pubsubsrv_topic", None)?;
    let client = node.create_client::<std_srvs::srv::Empty>("pubsubsrv_service", None)?;

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
            let request = std_srvs::srv::EmptyRequest::new().unwrap();

            // Take the client.
            let c = client.take().unwrap();

            // Send a request.
            match c.send(&request) {
                Ok(receiver) => {
                    // Make receiver single threaded.
                    let receiver = ST::new(receiver);

                    // Add the receiver.
                    selector_client.add_client_recv(&receiver);

                    // Wait a response with timeout.
                    match selector_client.wait_timeout(Duration::from_millis(100)) {
                        Ok(true) => match receiver.try_recv() {
                            RecvResult::Ok((c, _response, _header)) => {
                                // Received a response.
                                client = Some(c);
                            }
                            RecvResult::RetryLater(receiver) => {
                                // No correspondent response.
                                client = Some(receiver.give_up());
                            }
                            RecvResult::Err(e) => {
                                // Failed to receive.
                                pr_fatal!(logger, "{e}");
                                panic!();
                            }
                        },
                        Ok(false) => {
                            // Timeout.
                            client = Some(receiver.give_up());
                        }
                        Err(e) => {
                            // Failed to wait.
                            pr_error!(logger, "{e}");
                            client = Some(receiver.give_up());
                        }
                    }
                }
                Err(e) => {
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