# safe_drive: Formally Specified Rust Bindings for ROS2

`safe_drive` is a Rust bindings for ROS2.
This library provides formal specifications and tested the specifications by using a model checker.
Therefore, you can clearly understand how the scheduler work and the safeness of it.

## Specifications

Some algorithms we adopted are formally specified and tested the safeness by using TLA+.
Original ROS2's executor (rclcpp) is suffering from starvation.
In contrast, the starvation freedom of our executor has been validated by not only dynamic analysis but also
formal verification.

See [specifications](https://github.com/tier4/safe_drive/tree/main/specifications).

We specified and tested as follows.

- Single Threaded Callback Execution
  - Deadlock freedom
  - Starvation freedom
- Scheduling Core Algorithm
  - Validate the insertion algorithm
  - Termination
- Initialize Once
  - Deadlock freedom
  - Termination
  - Initialization is performed just once
