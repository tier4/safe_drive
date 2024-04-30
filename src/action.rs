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
