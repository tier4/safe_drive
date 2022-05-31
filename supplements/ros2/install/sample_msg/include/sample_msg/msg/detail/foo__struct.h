// generated from rosidl_generator_c/resource/idl__struct.h.em
// with input from sample_msg:msg/Foo.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__FOO__STRUCT_H_
#define SAMPLE_MSG__MSG__DETAIL__FOO__STRUCT_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>


// Constants defined in the message

// Include directives for member types
// Member 'a'
#include "rosidl_runtime_c/string.h"

// Struct defined in msg/Foo in the package sample_msg.
typedef struct sample_msg__msg__Foo
{
  rosidl_runtime_c__String a;
} sample_msg__msg__Foo;

// Struct for a sequence of sample_msg__msg__Foo.
typedef struct sample_msg__msg__Foo__Sequence
{
  sample_msg__msg__Foo * data;
  /// The number of valid items in data
  size_t size;
  /// The number of allocated items in data
  size_t capacity;
} sample_msg__msg__Foo__Sequence;

#ifdef __cplusplus
}
#endif

#endif  // SAMPLE_MSG__MSG__DETAIL__FOO__STRUCT_H_
