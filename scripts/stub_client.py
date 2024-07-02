import rclpy
from rclpy.action import ActionClient
from rclpy.node import Node

# $ . /safe_drive/supplements/ros2/install/setup.*sh
from example_msg.action import MyAction

import importlib

spec = importlib.util.find_spec("example_msg")
print(spec.origin)


class ExampleActionClient(Node):
    def __init__(self):
        super().__init__("safe_drive_example_action_client_py")
        self._action_client = ActionClient(self, MyAction, "safe_drive_example")

    def send_goal(self):
        self.get_logger().info("Waiting for action server...")

        self._action_client.wait_for_server()

        goal_msg = MyAction.Goal()
        goal_msg.a = 5

        self.get_logger().info("Sending goal request...")

        self._send_goal_future = self._action_client.send_goal_async(
            goal_msg, feedback_callback=self.feedback_callback
        )

        self._send_goal_future.add_done_callback(self.goal_response_callback)

    def goal_response_callback(self, future):
        goal_handle = future.result()
        if not goal_handle.accepted:
            self.get_logger().info("Goal rejected :(")
            return

        self.get_logger().info("Goal accepted :)")

        self._get_result_future = goal_handle.get_result_async()
        self._get_result_future.add_done_callback(self.get_result_callback)

    def get_result_callback(self, future):
        result = future.result().result
        self.get_logger().info(f"Result: {result}")
        rclpy.shutdown()

    def feedback_callback(self, feedback_msg):
        feedback = feedback_msg.feedback
        self.get_logger().info(f"Received feedback: {feedback}")


def main(args=None):
    rclpy.init(args=args)

    client = ExampleActionClient()
    client.send_goal()

    rclpy.spin(client)


if __name__ == "__main__":
    main()
