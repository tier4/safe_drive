// generated from rosidl_typesupport_introspection_c/resource/idl__type_support.c.em
// with input from sample_msg:msg/Num.idl
// generated code does not contain a copyright notice

#include <stddef.h>
#include "sample_msg/msg/detail/num__rosidl_typesupport_introspection_c.h"
#include "sample_msg/msg/rosidl_typesupport_introspection_c__visibility_control.h"
#include "rosidl_typesupport_introspection_c/field_types.h"
#include "rosidl_typesupport_introspection_c/identifier.h"
#include "rosidl_typesupport_introspection_c/message_introspection.h"
#include "sample_msg/msg/detail/num__functions.h"
#include "sample_msg/msg/detail/num__struct.h"


#ifdef __cplusplus
extern "C"
{
#endif

void Num__rosidl_typesupport_introspection_c__Num_init_function(
  void * message_memory, enum rosidl_runtime_c__message_initialization _init)
{
  // TODO(karsten1987): initializers are not yet implemented for typesupport c
  // see https://github.com/ros2/ros2/issues/397
  (void) _init;
  sample_msg__msg__Num__init(message_memory);
}

void Num__rosidl_typesupport_introspection_c__Num_fini_function(void * message_memory)
{
  sample_msg__msg__Num__fini(message_memory);
}

static rosidl_typesupport_introspection_c__MessageMember Num__rosidl_typesupport_introspection_c__Num_message_member_array[1] = {
  {
    "num",  // name
    rosidl_typesupport_introspection_c__ROS_TYPE_INT64,  // type
    0,  // upper bound of string
    NULL,  // members of sub message
    false,  // is array
    0,  // array size
    false,  // is upper bound
    offsetof(sample_msg__msg__Num, num),  // bytes offset in struct
    NULL,  // default value
    NULL,  // size() function pointer
    NULL,  // get_const(index) function pointer
    NULL,  // get(index) function pointer
    NULL  // resize(index) function pointer
  }
};

static const rosidl_typesupport_introspection_c__MessageMembers Num__rosidl_typesupport_introspection_c__Num_message_members = {
  "sample_msg__msg",  // message namespace
  "Num",  // message name
  1,  // number of fields
  sizeof(sample_msg__msg__Num),
  Num__rosidl_typesupport_introspection_c__Num_message_member_array,  // message members
  Num__rosidl_typesupport_introspection_c__Num_init_function,  // function to initialize message memory (memory has to be allocated)
  Num__rosidl_typesupport_introspection_c__Num_fini_function  // function to terminate message instance (will not free memory)
};

// this is not const since it must be initialized on first access
// since C does not allow non-integral compile-time constants
static rosidl_message_type_support_t Num__rosidl_typesupport_introspection_c__Num_message_type_support_handle = {
  0,
  &Num__rosidl_typesupport_introspection_c__Num_message_members,
  get_message_typesupport_handle_function,
};

ROSIDL_TYPESUPPORT_INTROSPECTION_C_EXPORT_sample_msg
const rosidl_message_type_support_t *
ROSIDL_TYPESUPPORT_INTERFACE__MESSAGE_SYMBOL_NAME(rosidl_typesupport_introspection_c, sample_msg, msg, Num)() {
  if (!Num__rosidl_typesupport_introspection_c__Num_message_type_support_handle.typesupport_identifier) {
    Num__rosidl_typesupport_introspection_c__Num_message_type_support_handle.typesupport_identifier =
      rosidl_typesupport_introspection_c__identifier;
  }
  return &Num__rosidl_typesupport_introspection_c__Num_message_type_support_handle;
}
#ifdef __cplusplus
}
#endif
