import rclpy
from rclpy.node import Node
from rclpy.action import ActionClient
from action_msgs.msg import GoalStatusArray

# make sure to source ../supplements/ros2/install/setup.*sh in advance
from example_msg.action import MyAction


class ActionStatusMonitor(Node):
    def __init__(self):
        super().__init__("action_status_monitor")
        self.action_client = ActionClient(self, MyAction, "/safe_drive_example")
        self.status_subscription = self.create_subscription(
            GoalStatusArray,
            "/safe_drive_example/_action/status",
            self.status_callback,
            10,
        )
        self.status_subscription  # prevent unused variable warning

    def status_callback(self, msg):
        if not msg.status_list:
            self.get_logger().info("No active goals found")
            return

        status = msg.status_list[-1]
        goal_id = status.goal_info.goal_id.uuid
        status_string = self.goal_status_to_string(status.status)
        self.get_logger().info(f"Goal {goal_id}: {status_string}")

    @staticmethod
    def goal_status_to_string(status):
        match status:
            case 0:
                return "Unknown"
            case 1:
                return "Accepted"
            case 2:
                return "Executing"
            case 3:
                return "Canceling"
            case 4:
                return "Succeeded"
            case 5:
                return "Canceled"
            case 6:
                return "Aborted"


def main(args=None):
    rclpy.init(args=args)
    action_status_monitor = ActionStatusMonitor()

    try:
        rclpy.spin(action_status_monitor)
    except KeyboardInterrupt:
        pass
    finally:
        action_status_monitor.destroy_node()
        rclpy.shutdown()


if __name__ == "__main__":
    main()
