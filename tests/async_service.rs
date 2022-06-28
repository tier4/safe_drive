pub mod common;

#[allow(unused_imports)]
use async_std::{future, prelude::*};
use safe_drive::{
    self,
    context::Context,
    error::DynError,
    service::{client::Client, server::Server},
};
use std::{error::Error, time::Duration};

const SERVICE_NAME: &str = "test_async_service";

#[test]
fn test_async() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
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
        let p = async_std::task::spawn(run_server(server));
        let s = async_std::task::spawn(run_client(client));
        p.await.unwrap();
        s.await.unwrap();
    });

    Ok(())
}

/// The server
async fn run_server(mut server: Server<common::ServiceType>) -> Result<(), DynError> {
    for _ in 0..3 {
        // receive a request
        let (sender, request) = server.recv().await?;
        println!("Server: request = {:?}", request);

        let response = common::Response {
            sum: request.a + request.b + request.c,
        };

        // send a response
        // send returns a new server to receive the next request
        println!("Server: response = {:?}", response);
        server = sender.send(&response)?;
    }

    Ok(())
}

/// The client
async fn run_client(mut client: Client<common::ServiceType>) -> Result<(), DynError> {
    let dur = Duration::from_millis(500);
    for n in 0..3 {
        let data = common::Request {
            a: n,
            b: n * 10,
            c: n * 100,
        };

        // send a request
        println!("Client: request = {:?}", data);
        let receiver = client.send(&data)?;

        // receive a response
        let (c, response) = receiver.recv().await?;
        println!("Client: response = {:?}", response);
        assert_eq!(response.sum, n + n * 10 + n * 100);

        // got a new client to send the next request
        client = c;

        // sleep 500[ms]
        async_std::task::sleep(dur).await;
    }

    Ok(())
}
