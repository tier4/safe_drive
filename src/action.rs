//! Actions

use crate::{
    error::RCLActionResult,
    msg::{interfaces::action_msgs::msg::GoalStatusSeq, ActionGoal, ActionMsg, ActionResult},
    rcl::{
        self, action_msgs__srv__CancelGoal_Request, rcl_action_goal_handle_t, rcl_action_server_t,
    },
};

pub mod client;
pub mod handle;
pub mod server;

pub type SendGoalServiceRequest<T> = <<T as ActionMsg>::Goal as ActionGoal>::Request;
type SendGoalServiceResponse<T> = <<T as ActionMsg>::Goal as ActionGoal>::Response;
type GetResultServiceRequest<T> = <<T as ActionMsg>::Result as ActionResult>::Request;
type GetResultServiceResponse<T> = <<T as ActionMsg>::Result as ActionResult>::Response;
pub type CancelRequest = action_msgs__srv__CancelGoal_Request;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum GoalStatus {
    Unknown = 0,
    Accepted = 1,
    Executing = 2,
    Canceling = 3,
    Succeeded = 4,
    Canceled = 5,
    Aborted = 6,
}

impl From<i8> for GoalStatus {
    fn from(s: i8) -> Self {
        match s {
            0 => GoalStatus::Unknown,
            1 => GoalStatus::Accepted,
            2 => GoalStatus::Executing,
            3 => GoalStatus::Canceling,
            4 => GoalStatus::Succeeded,
            5 => GoalStatus::Canceled,
            6 => GoalStatus::Aborted,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum GoalEvent {
    Execute = 0,
    CancelGoal = 1,
    Succeed = 2,
    Abort = 3,
    Canceled = 4,
}

impl From<i8> for GoalEvent {
    fn from(s: i8) -> Self {
        match s {
            0 => GoalEvent::Execute,
            1 => GoalEvent::CancelGoal,
            2 => GoalEvent::Succeed,
            3 => GoalEvent::Abort,
            4 => GoalEvent::Canceled,
            _ => unreachable!(),
        }
    }
}

pub(crate) fn update_goal_state(
    handle: *mut rcl_action_goal_handle_t,
    event: GoalEvent,
) -> RCLActionResult<()> {
    let guard = rcl::MT_UNSAFE_FN.lock();

    guard
        .rcl_action_update_goal_state(handle, event as u32)
        .unwrap();

    Ok(())
}

/// Set the status of the goals with the given IDs and publish the new status.
pub(crate) fn update_goal_status(
    server: *const rcl_action_server_t,
    goal_ids: &[[u8; 16]],
    new_status: GoalStatus,
) -> RCLActionResult<()> {
    let guard = rcl::MT_UNSAFE_FN.lock();

    let mut statuses = Box::new(rcl::MTSafeFn::rcl_action_get_zero_initialized_goal_status_array());
    guard
        .rcl_action_get_goal_status_array(server, statuses.as_mut())
        .unwrap();
    let status_seq_ptr = &mut statuses.msg.status_list as *mut _ as *mut GoalStatusSeq<0>;
    let status_seq = unsafe { &mut (*status_seq_ptr) };

    for status in status_seq.iter_mut() {
        if goal_ids
            .iter()
            .any(|id| *id == status.goal_info.goal_id.uuid)
        {
            status.status = new_status as i8;
        }
    }

    guard
        .rcl_action_publish_status(server, &statuses as *const _ as *const _)
        .unwrap();

    Ok(())
}
