SUBDIRS = tests/common

LIBDIR=supplements/ros2/install/example_msg/lib

export LD_LIBRARY_PATH := $(LIBDIR):$(LD_LIBRARY_PATH)
export SAFE_DRIVE_TEST := 1

all: $(SUBDIRS)
	cd supplements/ros2 && colcon build
	cargo build

$(SUBDIRS): FORCE
	$(MAKE) -C $@

FORCE:

test:
	# cargo test test_async_service -- --nocapture --exact
	cargo test --features custom_alloc -- --nocapture

check:
	cargo check

clippy:
	cargo clippy

doc: FORCE
	$(MAKE) -C mdbook
	cargo doc

clean:
	cargo clean
	rm -rf supplements/ros2/build supplements/ros2/install supplements/ros2/log
