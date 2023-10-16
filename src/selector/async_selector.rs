use super::{guard_condition::GuardCondition, CallbackResult};
use crate::{
    action,
    context::Context,
    error::DynError,
    service::{client::ClientData, server::ServerData},
    signal_handler,
    topic::subscriber::RCLSubscription,
};
use crossbeam_channel::{self, Receiver, Sender};
use once_cell::sync::Lazy;
use parking_lot::Mutex;
use std::{
    sync::Arc,
    thread::{self, yield_now, JoinHandle},
};

pub(crate) static SELECTOR: Lazy<Mutex<AsyncSelector>> =
    Lazy::new(|| Mutex::new(AsyncSelector::new()));

pub(crate) enum Command {
    Subscription(
        Arc<RCLSubscription>,
        Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
    ),
    RemoveSubscription(Arc<RCLSubscription>),
    Server(
        Arc<ServerData>,
        Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
    ),
    RemoveServer(Arc<ServerData>),
    Client(
        Arc<ClientData>,
        Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
    ),
    RemoveClient(Arc<ClientData>),
    ActionClient {
        data: Arc<action::client::ClientData>,
        feedback: Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
        status: Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
        goal: Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
        cancel: Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
        result: Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
    },
    RemoveActionClient(Arc<action::client::ClientData>),
    ActionServer {
        data: Arc<action::server::ServerData>,
        goal: Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
        cancel: Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
        result: Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
    },
    RemoveActionServer(Arc<action::server::ServerData>),
    ConditionVar(
        GuardCondition,
        Box<dyn FnMut() -> CallbackResult + Send + Sync + 'static>,
    ),
    RemoveConditionVar(GuardCondition),
    Halt,
}

struct SelectorData {
    tx: Sender<Command>,
    th: JoinHandle<Result<(), DynError>>,
    cond: GuardCondition,
    _context: Arc<Context>,
}

pub(crate) struct AsyncSelector {
    data: Option<SelectorData>,
}

unsafe impl Sync for AsyncSelector {}
unsafe impl Send for AsyncSelector {}

impl AsyncSelector {
    fn new() -> Self {
        AsyncSelector { data: None }
    }

    pub(crate) fn halt(&mut self) -> Result<(), DynError> {
        if let Some(SelectorData { tx, cond, th, .. }) = self.data.take() {
            tx.send(Command::Halt)?;
            cond.trigger()?;

            yield_now();
            let _ = th.join();
        }

        Ok(())
    }

    pub(crate) fn send_command(
        &mut self,
        context: &Arc<Context>,
        cmd: Command,
    ) -> Result<(), DynError> {
        loop {
            if let Some(SelectorData { tx, cond, .. }) = &self.data {
                tx.send(cmd)?;
                cond.trigger()?;
                return Ok(());
            } else {
                if let Command::Halt = cmd {
                    return Ok(());
                }

                let (tx, rx) = crossbeam_channel::bounded(256);
                let guard = super::guard_condition::GuardCondition::new(context.clone())?;
                let ctx = context.clone();
                let guard2 = guard.clone();
                let th = thread::spawn(move || select(ctx, guard2, rx));
                self.data = Some(SelectorData {
                    tx,
                    th,
                    _context: context.clone(),
                    cond: guard,
                });
            }
        }
    }
}

fn select(
    context: Arc<Context>,
    guard: GuardCondition,
    rx: Receiver<Command>,
) -> Result<(), DynError> {
    let mut selector = super::Selector::new(context)?;

    selector.add_guard_condition(&guard, None, false);

    loop {
        for cmd in rx.try_iter() {
            match cmd {
                Command::Subscription(s, h) => selector.add_rcl_subscription(s, Some(h), true),
                Command::RemoveSubscription(s) => selector.remove_rcl_subscription(&s),
                Command::Server(s, h) => selector.add_server_data(s, Some(h), true),
                Command::RemoveServer(s) => selector.remove_server_data(&s),
                Command::Client(c, h) => selector.add_client_data(c, Some(h), true),
                Command::RemoveClient(c) => selector.remove_client_data(&c),
                Command::ActionClient {
                    data,
                    feedback,
                    status,
                    goal,
                    cancel,
                    result,
                } => selector.add_action_client_data(
                    data,
                    Some(feedback),
                    Some(status),
                    Some(goal),
                    Some(cancel),
                    Some(result),
                ),
                Command::RemoveActionClient(c) => selector.remove_action_client_data(&c),
                Command::ActionServer {
                    data,
                    goal,
                    cancel,
                    result,
                } => selector.add_action_server_data(data, Some(goal), Some(cancel), Some(result)),
                Command::RemoveActionServer(s) => selector.remove_action_server_data(&s),
                Command::ConditionVar(c, h) => selector.add_guard_condition(&c, Some(h), true),
                Command::RemoveConditionVar(c) => selector.remove_guard_condition(&c),
                Command::Halt => return Ok(()),
            }
        }

        if let Err(_e) = selector.wait() {
            if signal_handler::is_halt() {
                for (_, h) in selector.subscriptions.iter_mut() {
                    if let Some(handler) = &mut h.handler {
                        (*handler)();
                    }
                }

                for (_, h) in selector.services.iter_mut() {
                    if let Some(handler) = &mut h.handler {
                        (*handler)();
                    }
                }

                for (_, h) in selector.clients.iter_mut() {
                    if let Some(handler) = &mut h.handler {
                        (*handler)();
                    }
                }

                for (_, h) in selector.cond.iter_mut() {
                    if let Some(handler) = &mut h.handler {
                        (*handler)();
                    }
                }

                return Ok(());
            }
        }
    }
}
