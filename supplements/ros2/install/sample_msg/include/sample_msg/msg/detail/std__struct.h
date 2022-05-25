// generated from rosidl_generator_c/resource/idl__struct.h.em
// with input from sample_msg:msg/Std.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__STD__STRUCT_H_
#define SAMPLE_MSG__MSG__DETAIL__STD__STRUCT_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>


// Constants defined in the message

// Include directives for member types
// Member 'l'
#include "rosidl_runtime_c/string.h"
// Member 'o'
#include "rosidl_runtime_c/primitives_sequence.h"
// Member 'q'
#include "std_msgs/msg/detail/bool__struct.h"
// Member 'r'
#include "std_msgs/msg/detail/byte__struct.h"
// Member 's'
#include "std_msgs/msg/detail/byte_multi_array__struct.h"
// Member 't'
#include "std_msgs/msg/detail/char__struct.h"
// Member 'u'
#include "std_msgs/msg/detail/color_rgba__struct.h"
// Member 'w'
#include "std_msgs/msg/detail/empty__struct.h"
// Member 'x'
#include "std_msgs/msg/detail/float32__struct.h"
// Member 'y'
#include "std_msgs/msg/detail/float32_multi_array__struct.h"
// Member 'z'
#include "std_msgs/msg/detail/float64__struct.h"
// Member 'aa'
#include "std_msgs/msg/detail/float64_multi_array__struct.h"
// Member 'bb'
#include "std_msgs/msg/detail/header__struct.h"
// Member 'cc'
#include "std_msgs/msg/detail/int16__struct.h"
// Member 'dd'
#include "std_msgs/msg/detail/int16_multi_array__struct.h"
// Member 'ee'
#include "std_msgs/msg/detail/int32__struct.h"
// Member 'ff'
#include "std_msgs/msg/detail/int32_multi_array__struct.h"
// Member 'gg'
#include "std_msgs/msg/detail/int64__struct.h"
// Member 'hh'
#include "std_msgs/msg/detail/int64_multi_array__struct.h"
// Member 'ii'
#include "std_msgs/msg/detail/int8__struct.h"
// Member 'jj'
#include "std_msgs/msg/detail/int8_multi_array__struct.h"
// Member 'kk'
#include "std_msgs/msg/detail/multi_array_dimension__struct.h"
// Member 'll'
#include "std_msgs/msg/detail/multi_array_layout__struct.h"
// Member 'mm'
#include "std_msgs/msg/detail/string__struct.h"
// Member 'oo'
#include "std_msgs/msg/detail/u_int16__struct.h"
// Member 'pp'
#include "std_msgs/msg/detail/u_int16_multi_array__struct.h"
// Member 'qq'
#include "std_msgs/msg/detail/u_int32__struct.h"
// Member 'rr'
#include "std_msgs/msg/detail/u_int32_multi_array__struct.h"
// Member 'ss'
#include "std_msgs/msg/detail/u_int64__struct.h"
// Member 'tt'
#include "std_msgs/msg/detail/u_int64_multi_array__struct.h"
// Member 'uu'
#include "std_msgs/msg/detail/u_int8__struct.h"
// Member 'vv'
#include "std_msgs/msg/detail/u_int8_multi_array__struct.h"

// Struct defined in msg/Std in the package sample_msg.
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

// Struct for a sequence of sample_msg__msg__Std.
typedef struct sample_msg__msg__Std__Sequence
{
  sample_msg__msg__Std * data;
  /// The number of valid items in data
  size_t size;
  /// The number of allocated items in data
  size_t capacity;
} sample_msg__msg__Std__Sequence;

#ifdef __cplusplus
}
#endif

#endif  // SAMPLE_MSG__MSG__DETAIL__STD__STRUCT_H_
