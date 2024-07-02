import time
import rclpy
from rclpy.action import ActionServer
from rclpy.node import Node

# $ . /safe_drive/supplements/ros2/install/setup.*sh
from example_msg.action import MyAction


class ExampleActionServer(Node):
    def __init__(self):
        super().__init__("safe_drive_example_action_server_py")
        self._action_server = ActionServer(
            self, MyAction, "safe_drive_example", self.execute_callback
        )

    def execute_callback(self, goal_handle):
        self.get_logger().info("Executing goal...")

        feedback_msg = MyAction.Feedback()

        for i in range(6):
            feedback_msg.c = i
            self.get_logger().info(f"Feedback: {feedback_msg}")
            goal_handle.publish_feedback(feedback_msg)
            time.sleep(1)

        goal_handle.succeed()

        result = MyAction.Result()
        result.b = 100
        return result


def main(args=None):
    rclpy.init(args=args)

    server = ExampleActionServer()

    rclpy.spin(server)


if __name__ == "__main__":
    main()
