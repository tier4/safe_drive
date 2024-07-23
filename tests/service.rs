pub mod common;

use common::msgs::example_msg::srv::{AddThreeIntsRequest, AddThreeIntsResponse};
use safe_drive::{context::Context, error::DynError, RecvResult};
use std::time::Duration;

const SERVICE_NAME1: &str = "test_service1";

#[test]
fn test_service() -> Result<(), DynError> {
    // create a context
    let ctx = Context::new()?;

    // create a server node
    let node_server = ctx.create_node("test_service_server_node", None, Default::default())?;

    // create a client node
    let node_client = ctx.create_node("test_service_client_node", None, Default::default())?;

    // create a server and a client
    let server = common::create_server(node_server, SERVICE_NAME1)?;
    let client = common::create_client(node_client, SERVICE_NAME1)?;

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
    selector.wait()?;

    std::thread::sleep(Duration::from_millis(1));

    // Client: receive the response
    match rcv_client.try_recv() {
        RecvResult::Ok((_, data, header)) => {
            println!("Client: sum = {}, header = {:?}", data.sum, header);
            assert_eq!(data.sum, 8);
            Ok(())
        }
        RecvResult::RetryLater(_) => {
            println!("should retry");
            Ok(())
        }
        RecvResult::Err(e) => Err(e.into()),
    }
}
