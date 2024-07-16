pub mod common;

use common::action_msg::action::my_action::*;
use futures::Future;
use safe_drive::{
    self,
    action::{
        client::{Client, ClientGoalRecv, ClientResultRecv},
        handle::GoalHandle,
        server::{Server, ServerQosOption},
        GoalStatus,
    },
    context::Context,
    error::DynError,
    msg::{
        builtin_interfaces::UnsafeTime,
        interfaces::action_msgs::{msg::GoalInfo, srv::CancelGoalRequest},
        unique_identifier_msgs::msg::UUID,
        GetUUID,
    },
};
use std::{pin::Pin, sync::Arc, thread, time::Duration};

fn create_server(
    ctx: &Arc<Context>,
    node: &str,
    action: &str,
    qos: Option<ServerQosOption>,
) -> Result<Server<MyAction>, DynError> {
    let node_server = ctx.create_node(node, None, Default::default()).unwrap();

    Server::new(node_server, action, qos).map_err(|e| e.into())
}

fn create_client(
    ctx: &Arc<Context>,
    node: &str,
    action: &str,
) -> Result<Client<MyAction>, DynError> {
    let node_client = ctx.create_node(node, None, Default::default())?;
    Client::new(node_client, action, None).map_err(|e| e.into())
}

async fn assert_status(client: Client<MyAction>, expected: GoalStatus) -> Client<MyAction> {
    let recv = client.recv_status();
    match async_std::future::timeout(Duration::from_secs(3), recv).await {
        Ok(Ok((c, status_array))) => {
            let list = status_array.status_list.as_slice();
            assert!(list.len() > 0);
            let status = list.last().unwrap().status;
            assert_eq!(status, expected as i8);
            c
        }
        Ok(Err(e)) => panic!("{e:?}"),
        Err(_) => panic!("timed out"),
    }
}

fn spawn_worker(handle: GoalHandle<MyAction>) {
    std::thread::Builder::new()
        .name("worker".into())
        .spawn(move || {
            for c in 0..=5 {
                if handle.is_canceling().unwrap() {
                    println!("server worker: canceling the goal");
                    handle.canceled(MyAction_Result { b: 1000 }).unwrap();
                    return;
                }

                println!("server worker: sending feedback {c}");
                let feedback = MyAction_Feedback { c };
                handle.feedback(feedback).unwrap();
                std::thread::sleep(Duration::from_secs(1));
            }

            println!("server worker: result is now available");
            handle.finish(MyAction_Result { b: 500 }).unwrap();

            loop {
                std::thread::sleep(Duration::from_secs(5));
            }
        })
        .unwrap();
}

async fn run_server(server: Server<MyAction>) -> Result<(), DynError> {
    let goal = async_std::task::spawn({
        let mut server_ = server.clone();
        async move {
            loop {
                let result = server_.recv_goal_request().await;
                match result {
                    Ok((sender, req)) => {
                        println!("server: goal received: {:?}", req);

                        let s = sender
                            .accept(|handle| {
                                if abort {
                                    spawn_worker_abort(handle)
                                } else {
                                    spawn_worker(handle)
                                }
                            })
                            .map_err(|(_sender, err)| err)
                            .expect("could not accept");
                        // let s = sender.reject().map_err(|(_sender, err)| err)?;

                        println!("server: goal response sent");

                        server_ = s;
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
        }
    });

    let cancel = async_std::task::spawn({
        let mut server_ = server.clone();
        async move {
            loop {
                let result = server_.recv_cancel_request().await;
                match result {
                    Ok((sender, candidates)) => {
                        println!("server: received cancel request for: {:?}", candidates);

                        let accepted = candidates; // filter requests if needed

                        sender
                            .accept(&accepted)
                            .expect("could not set status to CANCELING");

                        // perform shutdown operations for the goals here if needed
                        thread::sleep(Duration::from_secs(1));

                        // return cancel response
                        let s = sender
                            .send(accepted)
                            .map_err(|(_s, err)| err)
                            .expect("could not send cancel response");
                        println!("server: cancel response sent");

                        server_ = s;
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
        }
    });

    let result = async_std::task::spawn({
        let mut server_ = server.clone();
        async move {
            loop {
                let result = server_.recv_result_request().await;
                match result {
                    Ok((sender, req)) => {
                        println!("server: received result request for: {:?}", req);

                        // return result response
                        let s = sender
                            .send(req.get_uuid())
                            .map_err(|(_s, err)| err)
                            .expect("could not send");
                        println!("server: result response sent");

                        server_ = s;
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
        }
    });

    let _ = goal.await;
    let _ = cancel.await;
    let _ = result.await;

    Ok(())
}

async fn receive_goal_response(receiver: ClientGoalRecv<MyAction>) -> Client<MyAction> {
    let recv = receiver.recv();
    match async_std::future::timeout(Duration::from_secs(3), recv).await {
        Ok(Ok((c, response, _header))) => {
            println!("client: goal response received: {:?}", response);
            c
        }
        Ok(Err(e)) => panic!("{e:?}"),
        Err(_) => panic!("timed out"),
    }
}

async fn receive_result_response(receiver: ClientResultRecv<MyAction>) -> Client<MyAction> {
    let recv = receiver.recv();
    match async_std::future::timeout(Duration::from_secs(3), recv).await {
        Ok(Ok((c, response, _header))) => {
            println!("client: result response received: {:?}", response);
            c
        }
        Ok(Err(e)) => panic!("{e:?}"),
        Err(_) => panic!("timed out"),
    }
}

async fn run_client(client: Client<MyAction>) -> Result<(), DynError> {
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let receiver = client.send_goal_with_uuid(goal, uuid)?;

    let mut client = receive_goal_response(receiver).await;

    // receive feedback
    loop {
        let recv = client.recv_feedback();
        client = match async_std::future::timeout(Duration::from_secs(3), recv).await {
            Ok(Ok((c, feedback))) => {
                println!("client: feedback received: {:?}", feedback);

                if feedback.feedback.c == 5 {
                    client = c;
                    break;
                }
                c
            }
            Ok(Err(e)) => panic!("{e:?}"),
            Err(_) => panic!("timed out"),
        };
    }

    thread::sleep(Duration::from_secs(4));

    // send a result request
    println!("sending result request...");
    let receiver = client.send_result_request(&MyAction_GetResult_Request {
        goal_id: UUID { uuid },
    })?;

    let _ = receive_result_response(receiver).await;

    Ok(())
}

async fn run_client_cancel(client: Client<MyAction>) -> Result<(), DynError> {
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let receiver = client.send_goal_with_uuid(goal, uuid)?;

    let client = receive_goal_response(receiver).await;
    thread::sleep(Duration::from_secs(1));

    // send a cancel request
    let receiver = client.send_cancel_request(&CancelGoalRequest {
        goal_info: GoalInfo {
            goal_id: UUID { uuid },
            stamp: UnsafeTime { sec: 0, nanosec: 0 },
        },
    })?;
    println!("client: cancel request sent");

    let client = match receiver.recv().await {
        Ok((c, resp, _header)) => {
            println!("client: cancel response received: {:?}", resp);
            c
        }
        Err(e) => panic!("client: could not cancel the goal: {e:?}"),
    };

    let _ = assert_status(client, GoalStatus::Canceled).await;

    Ok(())
}

async fn run_client_status(client: Client<MyAction>) -> Result<(), DynError> {
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let receiver = client.send_goal_with_uuid(goal, uuid)?;

    let client = receive_goal_response(receiver).await;
    std::thread::sleep(Duration::from_secs(1));

    // wait for the task to finish
    let client = assert_status(client, GoalStatus::Executing).await;
    std::thread::sleep(Duration::from_secs(10));

    let _ = assert_status(client, GoalStatus::Succeeded).await;

    Ok(())
}

async fn run_client_abort(client: Client<MyAction>) -> Result<(), DynError> {
    let uuid: [u8; 16] = rand::random();
    let goal = MyAction_Goal { a: 10 };
    let receiver = client.send_goal_with_uuid(goal, uuid)?;

    let client = receive_goal_response(receiver).await;
    std::thread::sleep(Duration::from_secs(1));

    let client = assert_status(client, GoalStatus::Executing).await;
    std::thread::sleep(Duration::from_secs(3));

    let _ = assert_status(client, GoalStatus::Aborted).await;

    Ok(())
}

fn start_server_client<G>(
    action: &str,
    client_node: &str,
    server_node: &str,
    run_client_fn: G,
    server_abort: bool,
) -> Result<(), DynError>
where
    G: FnOnce(Client<MyAction>) -> Pin<Box<dyn Future<Output = Result<(), DynError>> + Send>>
        + Send
        + 'static,
{
    let ctx = Context::new().unwrap();
    let client = create_client(&ctx, client_node, action).unwrap();
    let server = create_server(&ctx, server_node, action, None).unwrap();

    async_std::task::block_on(async {
        let (tx, rx) = crossbeam_channel::unbounded();

        async_std::task::spawn({
            let server = server.clone();
            run_server(server, server_abort)
        });
        async_std::task::spawn(async move {
            let ret = run_client_fn(client).await;
            let _ = tx.send(());
            ret
        });

        let _ = rx.recv();
    });

    Ok(())
}

#[test]
fn test_async_action() -> Result<(), DynError> {
    start_server_client(
        "test_async_action",
        "test_async_action_client",
        "test_async_action_server",
        |client| Box::pin(run_client(client)),
        false,
    )
}

#[test]
fn test_async_action_cancel() -> Result<(), DynError> {
    start_server_client(
        "test_async_action_cancel",
        "test_async_action_client_cancel",
        "test_async_action_server_cancel",
        |client| Box::pin(run_client_cancel(client)),
        false,
    )
}

#[test]
fn test_async_action_status() -> Result<(), DynError> {
    start_server_client(
        "test_async_action_status",
        "test_async_action_client_status",
        "test_async_action_server_status",
        |client| Box::pin(run_client_status(client)),
        false,
    )
}

    Ok(())
}
