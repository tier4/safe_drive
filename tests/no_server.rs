pub mod common;

use common::msgs::example_msg::srv::{AddThreeIntsRequest, AddThreeIntsResponse};
use safe_drive::{context::Context, error::DynError, RecvResult};
use std::time::Duration;

const SERVICE_NAME3: &str = "test_service3";

#[test]
fn test_no_server() -> Result<(), DynError> {
    // create a context
    let ctx = Context::new()?;

    // create a client and a server node
    let node_client = ctx.create_node("test_client_no_server_node", None, Default::default())?;
    let node_server = ctx.create_node("test_server_no_server_node", None, Default::default())?;

    // create a server and a client
    let client = common::create_client(node_client, SERVICE_NAME3)?;
    let server = common::create_server(node_server, SERVICE_NAME3)?;

    std::thread::sleep(Duration::from_millis(500));

    let req = AddThreeIntsRequest { a: 1, b: 2, c: 5 };
    let (client, seq) = client.send_ret_seq(&req).unwrap();
    println!("clinet:send: seq = {seq}");

    std::thread::sleep(Duration::from_millis(500));

    let srv;
    let request;
    match server.try_recv() {
        RecvResult::Ok((s, req, header)) => {
            println!("server:recv: seq = {:?}", header.get_sequence());
            srv = s;
            request = req;
        }
        RecvResult::RetryLater(_) => panic!("server:try_recv: retry later"),
        RecvResult::Err(e) => panic!("server:try_recv:error: {e}"),
    }

    std::thread::sleep(Duration::from_millis(50));

    let client = client.give_up();
    println!("client: gave up!");

    let req = AddThreeIntsRequest { a: 4, b: 8, c: 10 };
    let (client, seq) = client.send_ret_seq(&req).unwrap();
    println!("clinet:send: seq = {seq}");

    std::thread::sleep(Duration::from_millis(50));

    let resp = AddThreeIntsResponse {
        sum: request.a + request.b + request.c,
    };
    let _ = srv.send(&resp);

    std::thread::sleep(Duration::from_millis(50));

    match client.try_recv() {
        RecvResult::Ok((_, msg, header)) => {
            panic!(
                "try_recv: msg = {:?}, seq = {:?}",
                msg,
                header.get_sequence()
            );
        }
        RecvResult::Err(_e) => {
            panic!("try_recv: error");
        }
        RecvResult::RetryLater(_) => {
            println!("try_recv: retry later");
        }
    }

    Ok(())
}
