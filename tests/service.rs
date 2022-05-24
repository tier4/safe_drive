pub mod common;

use safe_drive::{self, context::Context};
use std::error::Error;

const SERVICE_NAME: &str = "test_service";

#[test]
fn test_service() -> Result<(), Box<dyn Error>> {
    // create a context
    let ctx = Context::new()?;

    // create a server node
    let node_server = ctx.create_node("test_service_server_node", None, Default::default())?;

    // create a client node
    let node_client = ctx.create_node("test_service_client_node", None, Default::default())?;

    // create a server and a client
    let server = common::create_server(node_server, SERVICE_NAME)?;
    let client = common::create_client(node_client, SERVICE_NAME)?;

    // create a selector
    let mut selector = ctx.create_selector()?;

    // Client: send a request
    let req = common::Request { a: 1, b: 2, c: 5 };
    let rcv_client = match client.send_with_seq(req) {
        Ok((c, seq)) => {
            println!("Client: seq = {seq}");
            c
        }
        Err(e) => {
            return Err(e.into());
        }
    };

    // Server: wait the request
    selector.add_server(&server, None, true);
    selector.wait(None)?;

    // Server: receive the request
    match server.try_recv_with_header() {
        Ok((srv_send, data, header)) => {
            println!("Server: received: data = {:?}, header = {:?}", data, header);
            let response = common::Response {
                sum: data.a + data.b + data.c,
            };

            // Server: send a response
            let _ = srv_send.send(response);
        }
        Err(e) => {
            return Err(e.into());
        }
    }

    // Client: wait the response
    selector.add_client(&rcv_client, None, true);
    selector.wait(None)?;

    // Client: receive the response
    match rcv_client.try_recv_with_header() {
        Ok((_, data, header)) => {
            println!("Client: sum = {}, header = {:?}", data.sum, header);
            assert_eq!(data.sum, 8);
            Ok(())
        }
        Err(e) => Err(e.into()),
    }
}
