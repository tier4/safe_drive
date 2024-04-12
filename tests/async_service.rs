pub mod common;

#[allow(unused_imports)]
use async_std::{future, prelude::*};
use common::msgs::example_msg::srv::{AddThreeInts, AddThreeIntsRequest, AddThreeIntsResponse};
use safe_drive::{
    context::Context,
    error::DynError,
    logger::Logger,
    msg::common_interfaces::std_srvs,
    pr_error, pr_info,
    service::{client::Client, server::Server},
};
use std::{error::Error, time::Duration};

const SERVICE_NAME: &str = "test_async_service";

#[test]
fn test_async_service() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    // create a context
    let ctx = Context::new()?;

    // create nodes
    let node_server = ctx.create_node("test_async_server_node", None, Default::default())?;
    let node_client = ctx.create_node("test_async_client_node", None, Default::default())?;

    // create a server
    let server = common::create_server(node_server, SERVICE_NAME).unwrap();

    // create a client
    let client = common::create_client(node_client, SERVICE_NAME).unwrap();

    // create tasks
    async_std::task::block_on(async {
        let p = async_std::task::spawn(async {
            let _ = async_std::future::timeout(Duration::from_secs(3), run_server(server)).await;
        });
        let s = async_std::task::spawn(run_client(client));
        p.await;
        s.await.unwrap();
    });

    println!("finished test_async_service");

    Ok(())
}

/// The server
async fn run_server(mut server: Server<AddThreeInts>) -> Result<(), DynError> {
    for _ in 0..3 {
        // receive a request
        let (sender, request, _) = server.recv().await?;
        println!("Server: request = {:?}", request);

        let response = AddThreeIntsResponse {
            sum: request.a + request.b + request.c,
        };

        // send a response
        // send returns a new server to receive the next request
        println!("Server: response = {:?}", response);
        match sender.send(&response) {
            Ok(s) => server = s,
            Err((s, _e)) => server = s.give_up(),
        }
    }

    Ok(())
}

/// The client
async fn run_client(mut client: Client<AddThreeInts>) -> Result<(), DynError> {
    let dur = Duration::from_millis(500);
    for n in 0..3 {
        let data = AddThreeIntsRequest {
            a: n,
            b: n * 10,
            c: n * 100,
        };

        // send a request
        println!("Client: request = {:?}", data);
        let receiver = client.send(&data)?;

        // Create a logger.
        let logger = Logger::new("test_async_service::run_client");

        // receive a response
        let mut receiver = receiver.recv();
        match async_std::future::timeout(dur, &mut receiver).await {
            Ok(Ok((c, response, _header))) => {
                pr_info!(logger, "received: {:?}", response);
                assert_eq!(response.sum, n + n * 10 + n * 100);

                // got a new client to send the next request
                client = c;
            }
            Ok(Err(e)) => {
                pr_error!(logger, "error: {e}");
                break;
            }
            Err(_) => {
                client = receiver.give_up();
                continue;
            }
        }

        // sleep 500[ms]
        async_std::task::sleep(dur).await;
    }

    Ok(())
}

#[test]
fn test_client_rs() {
    // Create a context.
    let ctx = Context::new().unwrap();

    // Create a server node.
    let node = ctx
        .create_node("service_test_client_rs", None, Default::default())
        .unwrap();

    // Create a client.
    let client = node
        .create_client::<std_srvs::srv::Empty>("service_test_client_rs", None)
        .unwrap();

    // Create a logger.
    let logger = Logger::new("test_client_rs");

    async fn run_client(mut client: Client<std_srvs::srv::Empty>, logger: Logger) {
        let dur = Duration::from_millis(100);
        let mut n_timeout = 0;

        loop {
            let request = std_srvs::srv::EmptyRequest::new().unwrap();
            let mut receiver = client.send(&request).unwrap().recv();

            pr_info!(logger, "receiving");
            match async_std::future::timeout(dur, &mut receiver).await {
                Ok(Ok((c, response, _header))) => {
                    pr_info!(logger, "received: {:?}", response);
                    client = c;
                }
                Ok(Err(e)) => {
                    pr_error!(logger, "error: {e}");
                    break;
                }
                Err(_) => {
                    n_timeout += 1;
                    pr_info!(logger, "timeout: n = {n_timeout}");
                    if n_timeout > 10 {
                        return;
                    }
                    client = receiver.give_up();
                }
            }
        }
    }

    async_std::task::block_on(run_client(client, logger)); // Spawn an asynchronous task.

    println!("finished test_client_rs");
}
