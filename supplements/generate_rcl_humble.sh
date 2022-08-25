#!/bin/sh
#
# Generate ../src/rcl/humble.rs

bindgen /opt/ros/$ROS_DISTRO/include/rcl/rcl/rcl.h -o humble.rs -- \
-I/opt/ros/$ROS_DISTRO/include/rcl \
-I/opt/ros/$ROS_DISTRO/include/rcutils \
-I/opt/ros/$ROS_DISTRO/include/rmw \
-I/opt/ros/$ROS_DISTRO/include/rcl_yaml_param_parser \
-I/opt/ros/$ROS_DISTRO/include/rosidl_runtime_c \
-I/opt/ros/$ROS_DISTRO/include/rosidl_typesupport_interface

mv humble.rs ../src/rcl/humble.rs
