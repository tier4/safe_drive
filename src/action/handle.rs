use std::sync::Arc;

use super::server::ActionServerData;
use crate::{error::DynError, msg::ActionMsg, rcl};

/// GoalHandle contains information about an action goal and is used by server worker threads to send feedback and results.
pub struct GoalHandle<T: ActionMsg> {
    pub goal_id: [u8; 16],
    data: Arc<ActionServerData<T>>,
}

impl<T> GoalHandle<T>
where
    T: ActionMsg,
{
    pub(crate) fn new(goal_id: [u8; 16], data: Arc<ActionServerData<T>>) -> Self {
        Self { goal_id, data }
    }

    pub fn feedback(&self, mut content: T::Feedback) -> Result<(), DynError> {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_action_publish_feedback(
            unsafe { self.data.as_ptr_mut() },
            &mut content as *const _ as *mut _,
        )?;
        Ok(())
    }

    pub fn finish(&self, result: T::ResultContent) -> Result<(), DynError> {
        let mut results = self.data.results.lock();
        if let Some(_) = results.insert(self.goal_id, result) {
            return Err(format!(
                "the result for the goal (id: {:?}) already exists; it should be set only once",
                self.goal_id
            )
            .into());
        }
        Ok(())
    }

    pub fn abort() {
        todo!()
    }
}
