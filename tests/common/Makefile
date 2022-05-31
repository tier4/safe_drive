NUM_IN=../../supplements/ros2/src/sample_msg/msg/Num.msg
NUM_C=../../supplements/ros2/install/sample_msg/include/sample_msg/msg/num.h
NUM_RUST=num.rs

AddThreeInts_IN=../../supplements/ros2/src/sample_msg/srv/AddThreeInts.srv
AddThreeInts_C=../../supplements/ros2/install/sample_msg/include/sample_msg/srv/add_three_ints.h
AddThreeInts_RUST=add_three_ints.rs

INCLUDE=-I../../supplements/ros2/install/sample_msg/include -I/opt/ros/galactic/include/

all: $(NUM_RUST) $(AddThreeInts_RUST)

$(NUM_C): $(NUM_IN)
	cd ../../supplements/ros2 && colcon build --packages-select sample_msg

$(NUM_RUST): $(NUM_C)
	bindgen $(NUM_C) -- $(INCLUDE) > $(NUM_RUST)
	sh ../../supplements/bindgen/sed.sh $(NUM_RUST)

$(AddThreeInts_C): $(AddThreeInts_IN)
	cd ../../supplements/ros2 && colcon build --packages-select sample_msg

$(AddThreeInts_RUST): $(AddThreeInts_C)
	bindgen $(AddThreeInts_C) -- $(INCLUDE) > $(AddThreeInts_RUST)
	sh ../../supplements/bindgen/sed.sh $(AddThreeInts_RUST)
