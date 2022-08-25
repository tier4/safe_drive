all: msg.rs

.SUFFIXES: .rs .c

all: msg.rs
	cp msg.rs ../../src/msg/$(ROS_DISTRO)/runtime_c.rs

.c.rs:
	bindgen $< -o $@ -- -I/opt/ros/$(ROS_DISTRO)/include
	sh sed_crate.sh $@

msg.rs: msg.c

clean:
	rm -f *.rs
