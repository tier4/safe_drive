rm -rf src
mkdir src
cd src

git clone https://github.com/ros2/common_interfaces.git -b $ROS_DISTRO
ros2msg_to_rs --disable-common-interfaces -s crate -i common_interfaces -o ../src/msg/$ROS_DISTRO/common_interfaces

git clone https://github.com/ros2/rcl_interfaces.git -b $ROS_DISTRO
rm -rf rcl_interfaces/test_msgs rcl_interfaces/builtin_interfaces
ros2msg_to_rs --disable-common-interfaces -s crate -i rcl_interfaces -o ../src/msg/$ROS_DISTRO/interfaces

mkdir ros2msg && cd ros2msg
git clone https://github.com/ros2/unique_identifier_msgs.git -b $ROS_DISTRO
ros2msg_to_rs --disable-common-interfaces -s crate -i . -o ../src/msg/$ROS_DISTRO/ros2msg

echo "Files have been generated!"
echo "Run \"cargo fmt\""
