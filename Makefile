NUM_IN=supplements/ros2/src/sample_msg/msg/Num.msg
NUM_C=supplements/ros2/install/sample_msg/include/sample_msg/msg/num.h
NUM_RUST=tests/common/num.rs
NUM_LIBDIR=supplements/ros2/install/sample_msg/lib

AddThreeInts_IN=supplements/ros2/src/sample_msg/srv/AddThreeInts.srv
AddThreeInts_C=supplements/ros2/install/sample_msg/include/sample_msg/srv/add_three_ints.h
AddThreeInts_RUST=tests/common/add_three_ints.rs
AddThreeInts_LIBDIR=supplements/ros2/install/sample_msg/lib

INCLUDE=-I./supplements/ros2/install/sample_msg/include -I/opt/ros/galactic/include/


all: $(NUM_RUST) $(AddThreeInts_RUST)
	cargo build

$(NUM_C): $(NUM_IN)
	cd supplements/ros2 && colcon build --packages-select sample_msg

$(NUM_RUST): $(NUM_C)
	bindgen $(NUM_C) -- $(INCLUDE) > $(NUM_RUST)

$(AddThreeInts_C): $(AddThreeInts_IN)
	cd supplements/ros2 && colcon build --packages-select sample_msg

$(AddThreeInts_RUST): $(AddThreeInts_C)
	bindgen $(AddThreeInts_C) -- $(INCLUDE) > $(AddThreeInts_RUST)

test: all
	export LD_LIBRARY_PATH=$(NUM_LIBDIR):$(AddThreeInts_LIBDIR):$(LD_LIBRARY_PATH) && cargo test -- --nocapture

check:
	cargo check

clippy:
	cargo clippy

clean:
	cargo clean
	rm -rf supplements/ros2/build supplements/ros2/install supplements/ros2/log