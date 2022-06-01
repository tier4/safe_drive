SUBDIRS = tests/common supplements/bindgen

NUM_LIBDIR=supplements/ros2/install/sample_msg/lib
AddThreeInts_LIBDIR=supplements/ros2/install/sample_msg/lib

all: $(SUBDIRS)
	cd supplements/ros2 && colcon build
	cargo build

$(SUBDIRS):
	$(MAKE) -C $@

test: all
	export LD_LIBRARY_PATH=$(NUM_LIBDIR):$(AddThreeInts_LIBDIR):$(LD_LIBRARY_PATH) && cargo test -- --nocapture

check:
	cargo check

clippy:
	cargo clippy

clean:
	cargo clean
	rm -rf supplements/ros2/build supplements/ros2/install supplements/ros2/log
