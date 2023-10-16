use parking_lot::Mutex;
use std::{collections::BTreeMap, sync::Arc};

use super::{server::ServerData, update_goal_status, GoalStatus};
use crate::{error::DynError, msg::ActionMsg, rcl};

/// GoalHandle contains information about an action goal and is used by server worker threads to send feedback and results.
pub struct GoalHandle<T: ActionMsg> {
    pub goal_id: [u8; 16],
    data: Arc<ServerData>,
    pub results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,
}

impl<T> GoalHandle<T>
where
    T: ActionMsg,
{
    pub(crate) fn new(
        goal_id: [u8; 16],
        data: Arc<ServerData>,
        results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,
    ) -> Self {
        Self {
            goal_id,
            data,
            results,
        }
    }

    pub fn feedback(&self, content: T::FeedbackContent) -> Result<(), DynError> {
        let mut msg = <T as ActionMsg>::new_feedback_message(content, self.goal_id);

        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_action_publish_feedback(
            unsafe { self.data.as_ptr_mut() },
            &mut msg as *const _ as *mut _,
        )?;
        Ok(())
    }

    pub fn finish(&self, result: T::ResultContent) -> Result<(), DynError> {
        let mut results = self.results.lock();
        if results.insert(self.goal_id, result).is_some() {
            return Err(format!(
                "the result for the goal (id: {:?}) already exists; it should be set only once",
                self.goal_id
            )
            .into());
        }

        let server = unsafe { self.data.as_ptr_mut() };
        update_goal_status(server, &[self.goal_id], GoalStatus::Succeeded)?;

        Ok(())
    }

    pub fn abort() {
        todo!()
    }
}
