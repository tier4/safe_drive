//! Actions

use crate::{
    error::RCLActionResult,
    msg::{interfaces::action_msgs::msg::GoalStatusSeq, ActionGoal, ActionMsg, ActionResult},
    rcl::{
        self, bindgen_action_msgs__srv__CancelGoal_Request, rcl_action_goal_status_array_t,
        rcl_action_server_t,
    },
};

pub mod client;
pub mod handle;
pub mod server;

pub type SendGoalServiceRequest<T> = <<T as ActionMsg>::Goal as ActionGoal>::Request;
type SendGoalServiceResponse<T> = <<T as ActionMsg>::Goal as ActionGoal>::Response;
type GetResultServiceRequest<T> = <<T as ActionMsg>::Result as ActionResult>::Request;
type GetResultServiceResponse<T> = <<T as ActionMsg>::Result as ActionResult>::Response;
pub type CancelRequest = bindgen_action_msgs__srv__CancelGoal_Request;

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

pub(crate) fn update_goal_status(
    server: *const rcl_action_server_t,
    goal_ids: &[[u8; 16]],
    new_status: GoalStatus,
) -> RCLActionResult<()> {
    let guard = rcl::MT_UNSAFE_FN.lock();

    let mut statuses: rcl_action_goal_status_array_t =
        rcl::MTSafeFn::rcl_action_get_zero_initialized_goal_status_array();
    guard.rcl_action_get_goal_status_array(server, &mut statuses)?;
    let status_seq_ptr = &mut statuses.msg.status_list as *mut _ as *mut GoalStatusSeq<0>;
    let status_seq = unsafe { &mut (*status_seq_ptr) };

    for status in status_seq.iter_mut() {
        if goal_ids
            .iter()
            .any(|id| status.goal_info.goal_id.uuid.eq(id))
        {
            status.status = new_status as i8;
        }
    }
    guard.rcl_action_publish_status(server, &statuses as *const _ as *const _)?;

    Ok(())
}
