use parking_lot::Mutex;
use std::{collections::BTreeMap, sync::Arc};

use super::{server::ServerData, update_goal_state, update_goal_status, GoalEvent, GoalStatus};
use crate::{error::DynError, msg::ActionMsg, rcl};

/// GoalHandle contains information about an action goal and is used by server worker threads to send feedback and results.
pub struct GoalHandle<T: ActionMsg> {
    pub goal_id: [u8; 16],
    pub(crate) handle: *mut rcl::rcl_action_goal_handle_t,
    data: Arc<ServerData>,
    pub results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,
}

impl<T> GoalHandle<T>
where
    T: ActionMsg,
{
    pub(crate) fn new(
        goal_id: [u8; 16],
        goal_handle: *mut rcl::rcl_action_goal_handle_t,
        data: Arc<ServerData>,
        results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,
    ) -> Self {
        Self {
            goal_id,
            handle: goal_handle,
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

    pub fn canceled(&self, result: T::ResultContent) -> Result<(), DynError> {
        let mut results = self.results.lock();
        if results.insert(self.goal_id, result).is_some() {
            return Err(format!(
                "the result for the goal (id: {:?}) already exists; it should be set only once",
                self.goal_id
            )
            .into());
        }

        // let server = unsafe { self.data.as_ptr_mut() };
        // update_goal_status(server, &[self.goal_id], GoalStatus::Canceled)?;
        update_goal_state(self.handle, GoalEvent::Canceled)?;

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

        // let server = unsafe { self.data.as_ptr_mut() };
        // update_goal_status(server, &[self.goal_id], GoalStatus::Succeeded)?;
        update_goal_state(self.handle, GoalEvent::Succeed)?;

        Ok(())
    }

    pub fn is_canceling(&self) -> Result<bool, DynError> {
        let mut s: rcl::rcl_action_goal_state_t = 0; // default to UNKNOWN
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard
            .rcl_action_goal_handle_get_status(self.handle, &mut s)
            .unwrap();

        println!("status: {:?}", GoalStatus::from(s));

        Ok(GoalStatus::Canceling == GoalStatus::from(s))
    }

    pub fn abort() {
        todo!()
        // let server = unsafe { self.data.as_ptr_mut() };
        // let _ = update_goal_status(server, &[self.goal_id], GoalStatus::Aborted);
    }
}

impl<T> Drop for GoalHandle<T>
where
    T: ActionMsg,
{
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_action_goal_handle_fini(self.handle);
    }
}

unsafe impl<T> Send for GoalHandle<T> where T: ActionMsg {}
unsafe impl<T> Sync for GoalHandle<T> where T: ActionMsg {}
