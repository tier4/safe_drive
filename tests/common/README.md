1. run bindgen
2. rename `struct rosidl_message_type_support_t`
3. rename `struct rosidl_service_type_support_t`
3. add `pub use safe_drive::rcl::{rosidl_message_type_support_t, rosidl_service_type_support_t};`

.msg file:

```
# http://wiki.ros.org/msg
bool a
int8 b
uint8 c
int16 d
uint16 e
int32 f
uint32 g
int64 h
uint64 i
float32 j
float64 k
string l
# time m
# duration n

# array
int32[] o
int32[10] p

# http://wiki.ros.org/std_msgs
std_msgs/Bool q
std_msgs/Byte r
std_msgs/ByteMultiArray s
std_msgs/Char t
std_msgs/ColorRGBA u
# std_msgs/Duration v
std_msgs/Empty w
std_msgs/Float32 x
std_msgs/Float32MultiArray y
std_msgs/Float64 z
std_msgs/Float64MultiArray aa
std_msgs/Header bb
std_msgs/Int16 cc
std_msgs/Int16MultiArray dd
std_msgs/Int32 ee
std_msgs/Int32MultiArray ff
std_msgs/Int64 gg
std_msgs/Int64MultiArray hh
std_msgs/Int8 ii
std_msgs/Int8MultiArray jj
std_msgs/MultiArrayDimension kk
std_msgs/MultiArrayLayout ll
std_msgs/String mm
# std_msgs/Time nn
std_msgs/UInt16 oo
std_msgs/UInt16MultiArray pp
std_msgs/UInt32 qq
std_msgs/UInt32MultiArray rr
std_msgs/UInt64 ss
std_msgs/UInt64MultiArray tt
std_msgs/UInt8 uu
std_msgs/UInt8MultiArray vv
```

Translated C file.

```c
typedef struct sample_msg__msg__Std
{
  bool a;
  int8_t b;
  uint8_t c;
  int16_t d;
  uint16_t e;
  int32_t f;
  uint32_t g;
  int64_t h;
  uint64_t i;
  float j;
  double k;
  rosidl_runtime_c__String l;
  rosidl_runtime_c__int32__Sequence o;
  int32_t p[10];
  std_msgs__msg__Bool q;
  std_msgs__msg__Byte r;
  std_msgs__msg__ByteMultiArray s;
  std_msgs__msg__Char t;
  std_msgs__msg__ColorRGBA u;
  std_msgs__msg__Empty w;
  std_msgs__msg__Float32 x;
  std_msgs__msg__Float32MultiArray y;
  std_msgs__msg__Float64 z;
  std_msgs__msg__Float64MultiArray aa;
  std_msgs__msg__Header bb;
  std_msgs__msg__Int16 cc;
  std_msgs__msg__Int16MultiArray dd;
  std_msgs__msg__Int32 ee;
  std_msgs__msg__Int32MultiArray ff;
  std_msgs__msg__Int64 gg;
  std_msgs__msg__Int64MultiArray hh;
  std_msgs__msg__Int8 ii;
  std_msgs__msg__Int8MultiArray jj;
  std_msgs__msg__MultiArrayDimension kk;
  std_msgs__msg__MultiArrayLayout ll;
  std_msgs__msg__String mm;
  std_msgs__msg__UInt16 oo;
  std_msgs__msg__UInt16MultiArray pp;
  std_msgs__msg__UInt32 qq;
  std_msgs__msg__UInt32MultiArray rr;
  std_msgs__msg__UInt64 ss;
  std_msgs__msg__UInt64MultiArray tt;
  std_msgs__msg__UInt8 uu;
  std_msgs__msg__UInt8MultiArray vv;
} sample_msg__msg__Std;
```
