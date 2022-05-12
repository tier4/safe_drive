use crate::subscriber::RCLSubscription;
use std::{
    sync::{
        mpsc::{sync_channel, Receiver, SendError, SyncSender},
        Arc,
    },
    task::Waker,
    thread,
};

pub(crate) enum Op {
    Subscription(Arc<RCLSubscription>, Waker),
    Exit,
}

pub(crate) struct Selector {
    pub tx: SyncSender<Op>,
    is_exit: bool,
}

impl Selector {
    pub fn new() -> Self {
        let (tx, rx) = sync_channel(64);

        //thread::spawn(|| {});

        Selector { tx, is_exit: false }
    }

    pub fn select(&self, op: Op) -> Result<(), SendError<Op>> {
        self.tx.send(op)?;

        Ok(())
    }
}
