use std::sync::Arc;

use super::{
    server::{publish_status, ActionServerData},
    GoalStatus,
};
use crate::{
    error::DynError,
    msg::{interfaces::action_msgs::msg::GoalStatusSeq, ActionMsg},
    rcl::{self, rcl_action_goal_status_array_t},
};

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

        // publish_status(unsafe { self.data.as_ptr_mut() });

        let guard = rcl::MT_UNSAFE_FN.lock();

        let server = unsafe { self.data.as_ptr_mut() };
        let mut statuses: rcl_action_goal_status_array_t =
            rcl::MTSafeFn::rcl_action_get_zero_initialized_goal_status_array();
        guard.rcl_action_get_goal_status_array(server, &mut statuses)?;
        let status_seq_ptr = &mut statuses.msg.status_list as *mut _ as *mut GoalStatusSeq<0>;
        let status_seq = unsafe { &mut (*status_seq_ptr) };

        for status in status_seq.iter_mut() {
            if status.goal_info.goal_id.uuid == self.goal_id {
                status.status = GoalStatus::Succeeded.into();
                break;
            }
        }
        guard.rcl_action_publish_status(server, &statuses as *const _ as *const _)?;

        Ok(())
    }

    pub fn abort() {
        todo!()
    }
}
