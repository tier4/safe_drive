all: msgs.rs

msgs.rs: msgs.c
	bindgen msgs.c -o msgs.rs -- -I/opt/ros/galactic/include
	sh sed.sh msgs.rs

clean:
	rm -f *.rs
