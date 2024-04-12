pub mod common;

use common::msgs::example_msg::srv::{AddThreeIntsRequest, AddThreeIntsResponse};
use safe_drive::{context::Context, error::DynError, RecvResult};
use std::time::Duration;

const SERVICE_NAME2: &str = "test_service2";

#[test]
fn test_client_wait() -> Result<(), DynError> {
    // create a context
    let ctx = Context::new()?;

    // create a server node
    let node_server = ctx.create_node("test_client_wait_server_node", None, Default::default())?;

    // create a client node
    let node_client = ctx.create_node("test_client_wait_client_node", None, Default::default())?;

    // create a server and a client
    let server = common::create_server(node_server, SERVICE_NAME2)?;
    let client = common::create_client(node_client, SERVICE_NAME2)?;

    // create a selector
    let mut selector = ctx.create_selector()?;

    // Client: send a request
    let req = AddThreeIntsRequest { a: 1, b: 2, c: 5 };
    let rcv_client = match client.send_ret_seq(&req) {
        Ok((c, seq)) => {
            println!("Client: seq = {seq}");
            c
        }
        Err(e) => {
            return Err(e.into());
        }
    };

    // Server: wait the request
    selector.add_server(
        server,
        Box::new(move |request, header| {
            println!(
                "Server: received: data = {:?}, header = {:?}",
                request, header
            );
            AddThreeIntsResponse {
                sum: request.a + request.b + request.c,
            }
        }),
    );
    selector.wait()?; // Wait the request.

    std::thread::sleep(Duration::from_millis(1));

    match rcv_client.recv_timeout(Duration::from_millis(20), &mut selector) {
        RecvResult::Ok((_client, response, _)) => {
            println!("received: {}", response.sum);
            Ok(())
        }
        RecvResult::RetryLater(_rcv) => {
            println!("retry later");
            Ok(())
        }
        RecvResult::Err(e) => Err(e.into()),
    }
}
