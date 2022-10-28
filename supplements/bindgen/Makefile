all: msg.rs

.SUFFIXES: .rs .c

all: msg.rs rcl.rs
	cp msg.rs ../../src/msg/$(ROS_DISTRO)/runtime_c.rs
	cp rcl.rs ../../src/rcl/$(ROS_DISTRO).rs

.c.rs:
	bindgen --blocklist-function atexit $< -o $@ -- -I/opt/ros/$(ROS_DISTRO)/include
	sed -i -e 's/"\* */"a /'  $@

msg.rs: msg.c
	bindgen --blocklist-function atexit $< -o $@ -- -I/opt/ros/$(ROS_DISTRO)/include
	sh sed_crate.sh $@

clean:
	rm -f *.rs
