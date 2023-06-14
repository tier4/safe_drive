use std::sync::Arc;

use crossbeam_channel::Sender;

use crate::{error::DynError, msg::ActionMsg, rcl};

use super::server::ActionServerData;

/// GoalHandle contains information about an action goal and is used by server worker threads to send feedback and results.
pub struct GoalHandle<T: ActionMsg> {
    pub goal_id: [u8; 16],
    // server: *mut rcl::rcl_action_server_t,
    data: Arc<ActionServerData<T>>,
    tx: Sender<GoalHandleMessage<T>>,
}

impl<T> GoalHandle<T>
where
    T: ActionMsg,
{
    pub(crate) fn new(
        goal_id: [u8; 16],
        data: Arc<ActionServerData<T>>,
        tx: Sender<GoalHandleMessage<T>>,
    ) -> Self {
        Self { goal_id, data, tx }
    }

    pub fn feedback(&self, mut content: T::Feedback) -> Result<(), DynError> {
        // pub fn feedback(&self, content: T::Feedback) -> Result<(), SendError<GoalHandleMessage<T>>> {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_action_publish_feedback(
            unsafe { self.data.as_ptr_mut() },
            &mut content as *const _ as *mut _,
        )?;
        Ok(())
        // let msg = GoalHandleMessage {
        //     goal_id: self.goal_id,
        //     content: GoalHandleMessageContent::Feedback(content),
        // };
        // self.tx.send(msg)
    }

    pub fn finish(&self, result: T::ResultContent) -> Result<(), DynError> {
        let mut results = self.data.results.lock();
        if let Some(_) = results.insert(self.goal_id, result) {
            return Err(
                "the result for the goal already exists; it should be set only once".into(),
            );
        }
        Ok(())
        // let msg = GoalHandleMessage {
        //     goal_id: self.goal_id,
        //     content: GoalHandleMessageContent::Result(result),
        // };
        // self.tx.send(msg)
    }

    pub fn abort() {}
}

pub struct GoalHandleMessage<T: ActionMsg> {
    pub(crate) goal_id: [u8; 16],
    pub(crate) content: GoalHandleMessageContent<T>,
}

pub enum GoalHandleMessageContent<T: ActionMsg> {
    Feedback(T::Feedback),
    Result(T::ResultContent),
}
