use super::{guard_condition::GuardCondition, CallbackResult};
use crate::{
    context::Context,
    error::DynError,
    service::{client::ClientData, server::ServerData},
    signal_handler,
    topic::subscriber::RCLSubscription,
};
use flume::{self, Receiver, Sender};
use once_cell::sync::Lazy;
use parking_lot::Mutex;
use std::{
    collections::BTreeMap,
    sync::Arc,
    thread::{self, JoinHandle},
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
    Halt,
}

struct SelectorData {
    tx: Sender<Command>,
    _context: Arc<Context>,
    cond: Arc<GuardCondition>,
    th: JoinHandle<Result<(), DynError>>,
}

pub(crate) struct AsyncSelector {
    contexts: BTreeMap<usize, SelectorData>,
}

unsafe impl Sync for AsyncSelector {}
unsafe impl Send for AsyncSelector {}

impl AsyncSelector {
    fn new() -> Self {
        AsyncSelector {
            contexts: Default::default(),
        }
    }

    pub(crate) fn halt(&mut self, context: &Context) -> Result<(), DynError> {
        if let Some(SelectorData { tx, cond, th, .. }) = self.contexts.remove(&context.id) {
            tx.send(Command::Halt)?;
            cond.trigger()?;
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
            if let Some(SelectorData { tx, cond, .. }) = self.contexts.get(&context.id) {
                tx.send(cmd)?;
                cond.trigger()?;
                return Ok(());
            } else {
                if let Command::Halt = cmd {
                    return Ok(());
                }

                let (tx, rx) = flume::bounded(256);
                let guard = super::guard_condition::GuardCondition::new(context.clone())?;
                let ctx = context.clone();
                let guard2 = guard.clone();
                let th = thread::spawn(move || select(ctx, guard2, rx));
                self.contexts.insert(
                    context.id,
                    SelectorData {
                        tx,
                        _context: context.clone(),
                        cond: guard,
                        th,
                    },
                );
            }
        }
    }
}

fn select(
    context: Arc<Context>,
    guard: Arc<GuardCondition>,
    rx: Receiver<Command>,
) -> Result<(), DynError> {
    let mut selector = super::Selector::new(context)?;

    selector.add_guard_condition(&guard, None);

    loop {
        for cmd in rx.try_iter() {
            match cmd {
                Command::Subscription(s, h) => selector.add_rcl_subscription(s, Some(h), true),
                Command::RemoveSubscription(s) => selector.remove_rcl_subscription(&s),
                Command::Server(s, h) => selector.add_server_data(s, Some(h), true),
                Command::RemoveServer(s) => selector.remove_server_data(&s),
                Command::Client(c, h) => selector.add_client_data(c, Some(h), true),
                Command::RemoveClient(c) => selector.remove_client_data(&c),
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
            }
        }
    }
}
