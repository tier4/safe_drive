use parking_lot::Mutex;
use std::{collections::BTreeMap, rc::Rc, sync::Arc};

use super::{server::ServerData, GoalEvent, GoalStatus};
use crate::{
    error::{DynError, RCLActionError},
    msg::ActionMsg,
    rcl,
};

/// GoalHandle contains information about an action goal and is used by server worker threads to send feedback and results.
pub struct GoalHandle<T: ActionMsg> {
    pub goal_id: [u8; 16],
    pub(crate) handle: Rc<GoalHandleData>,
    data: Arc<ServerData>,
    pub results: Arc<Mutex<BTreeMap<[u8; 16], T::ResultContent>>>,
}

impl<T> Clone for GoalHandle<T>
where
    T: ActionMsg,
{
    fn clone(&self) -> Self {
        Self {
            goal_id: self.goal_id.clone(),
            handle: self.handle.clone(),
            data: self.data.clone(),
            results: self.results.clone(),
        }
    }
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
            handle: Rc::new(GoalHandleData(goal_handle)),
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

        self.update(GoalEvent::Canceled)?;
        self.data.publish_goal_status()?;

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

        self.update(GoalEvent::Succeed)?;
        self.data.publish_goal_status()?;

        Ok(())
    }

    pub fn is_canceling(&self) -> Result<bool, DynError> {
        let mut s: rcl::rcl_action_goal_state_t = GoalStatus::Unknown as i8;
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard
            .rcl_action_goal_handle_get_status(self.handle.0, &mut s)
            .unwrap();

        Ok(GoalStatus::Canceling == GoalStatus::from(s))
    }

    pub fn abort(&self) -> Result<(), RCLActionError> {
        self.update(GoalEvent::Abort)?;
        self.data.publish_goal_status()?;
        Ok(())
    }

    pub(crate) fn update(&self, event: GoalEvent) -> Result<(), RCLActionError> {
        self.handle.update_goal_state(event)
    }
}

unsafe impl<T> Send for GoalHandle<T> where T: ActionMsg {}
unsafe impl<T> Sync for GoalHandle<T> where T: ActionMsg {}

/// `GoalHandleData` wraps the pointer to `rcl_action_goal_handle_t` and finalizes it when dropped.
pub(crate) struct GoalHandleData(pub *mut rcl::rcl_action_goal_handle_t);

impl GoalHandleData {
    pub(crate) fn update_goal_state(&self, event: GoalEvent) -> Result<(), RCLActionError> {
        let guard = rcl::MT_UNSAFE_FN.lock();

        guard
            .rcl_action_update_goal_state(self.0, event as u32)
            .unwrap();

        Ok(())
    }
}

impl Drop for GoalHandleData {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_action_goal_handle_fini(self.0);
    }
}
