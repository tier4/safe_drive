# Pre-defined Data Structure

`safe_drive` provides basic types of ROS2 as follows.

`use safe_drive::msg;`

| ROS2                        | safe_drive                                             |
|-----------------------------|--------------------------------------------------------|
| unique_identifier_msgs/uuid | msg::ros2msg::unique_identifier_msgs::msg::uuid        |
| actionlib_msgs/*            | msg::common_interfaces::actionib_msgs::msg::*          |
| diagnostic_msgs/*           | msg::common_interfaces::diagnostic_msgs::{msg, srv}::* |
| geometry_msgs/*             | msg::common_interfaces::geometry_msgs::msg::*          |
| nav_msgs/*                  | msg::common_interfaces::nav_msgs::{msg, srv}::*        |
| sensor_msgs/*               | msg::common_interfaces::sensor_msgs::{msg, srv}::*     |
| shape_msgs/*                | msg::common_interfaces::shape_msgs::msg::*             |
| std_msgs/*                  | msg::common_interfaces::std_msgs::msg::*               |
| std_srvs/*                  | msg::common_interfaces::std_srvs::srv::*               |
| stereo_msgs/*               | msg::common_interfaces::stereo_msgs::msg::*            |
| trajectory_msgs/*           | msg::common_interfaces::trajectory_msgs::msg::*        |
| visualization_msgs/*        | msg::common_interfaces::visualization_msgs::msg::*     |

There are `msg` and `srv` modules like `sensor_msgs::msg` and `sensor_msgs::srv`.
`msg`s include data types of topics discussed in previous chapters,
and `srv`s include data types of services introduced from next chapter.
