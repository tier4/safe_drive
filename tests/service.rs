pub mod common;

use safe_drive::{self, context::Context, error::DynError, RecvResult, ST};
use std::time::Duration;

const SERVICE_NAME1: &str = "test_service1";
const SERVICE_NAME2: &str = "test_service2";
const SERVICE_NAME3: &str = "test_service3";

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
    let req = common::Request { a: 1, b: 2, c: 5 };
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
            common::Response {
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
    let req = common::Request { a: 1, b: 2, c: 5 };
    let rcv_client = match client.send_ret_seq(&req) {
        Ok((c, seq)) => {
            println!("Client: seq = {seq}");
            c
        }
        Err(e) => {
            return Err(e.into());
        }
    };

    // Make the client a single-threaded data.
    let rcv_client = ST::new(rcv_client);

    // Register the client
    selector.add_client_recv(&rcv_client);

    // Server: wait the request
    selector.add_server(
        server,
        Box::new(move |request, header| {
            println!(
                "Server: received: data = {:?}, header = {:?}",
                request, header
            );
            common::Response {
                sum: request.a + request.b + request.c,
            }
        }),
    );
    selector.wait()?; // Wait the request.

    std::thread::sleep(Duration::from_millis(1));

    selector.wait()?; // Wait the response.

    match rcv_client.try_recv() {
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

    let req = common::Request { a: 1, b: 2, c: 5 };
    let (client, seq) = client.send_ret_seq(&req).unwrap();
    println!("clinet:send: seq = {seq}");

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

    let req = common::Request { a: 4, b: 8, c: 10 };
    let (client, seq) = client.send_ret_seq(&req).unwrap();
    println!("clinet:send: seq = {seq}");

    std::thread::sleep(Duration::from_millis(50));

    let resp = common::Response {
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
