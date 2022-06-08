all: msg.rs builtin_interfaces.rs

.SUFFIXES: .rs .c

all: msg.rs
	cp msg.rs ../../src/msg/galactic/runtime_c.rs

.c.rs:
	bindgen $< -o $@ -- -I/opt/ros/galactic/include
	sh sed_crate.sh $@

msg.rs: msg.c

clean:
	rm -f *.rs
