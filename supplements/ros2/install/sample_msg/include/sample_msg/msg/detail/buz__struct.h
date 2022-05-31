// generated from rosidl_generator_c/resource/idl__struct.h.em
// with input from sample_msg:msg/Buz.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__BUZ__STRUCT_H_
#define SAMPLE_MSG__MSG__DETAIL__BUZ__STRUCT_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>


// Constants defined in the message

// Include directives for member types
// Member 'c'
#include "rosidl_runtime_c/string.h"

// Struct defined in msg/Buz in the package sample_msg.
typedef struct sample_msg__msg__Buz
{
  rosidl_runtime_c__String c;
} sample_msg__msg__Buz;

// Struct for a sequence of sample_msg__msg__Buz.
typedef struct sample_msg__msg__Buz__Sequence
{
  sample_msg__msg__Buz * data;
  /// The number of valid items in data
  size_t size;
  /// The number of allocated items in data
  size_t capacity;
} sample_msg__msg__Buz__Sequence;

#ifdef __cplusplus
}
#endif

#endif  // SAMPLE_MSG__MSG__DETAIL__BUZ__STRUCT_H_
