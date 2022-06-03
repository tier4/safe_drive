all: msgs.rs builtin_interfaces.rs

.SUFFIXES: .rs .c

all: msgs.rs
	cp msgs.rs ../../src/msgs/galactic.rs

.c.rs:
	bindgen $< -o $@ -- -I/opt/ros/galactic/include
	sh sed_crate.sh $@

msgs.rs: msgs.c

clean:
	rm -f *.rs
