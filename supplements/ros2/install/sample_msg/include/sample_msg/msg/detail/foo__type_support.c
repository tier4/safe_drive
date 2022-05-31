// generated from rosidl_typesupport_introspection_c/resource/idl__type_support.c.em
// with input from sample_msg:msg/Foo.idl
// generated code does not contain a copyright notice

#include <stddef.h>
#include "sample_msg/msg/detail/foo__rosidl_typesupport_introspection_c.h"
#include "sample_msg/msg/rosidl_typesupport_introspection_c__visibility_control.h"
#include "rosidl_typesupport_introspection_c/field_types.h"
#include "rosidl_typesupport_introspection_c/identifier.h"
#include "rosidl_typesupport_introspection_c/message_introspection.h"
#include "sample_msg/msg/detail/foo__functions.h"
#include "sample_msg/msg/detail/foo__struct.h"


// Include directives for member types
// Member `a`
#include "rosidl_runtime_c/string_functions.h"

#ifdef __cplusplus
extern "C"
{
#endif

void Foo__rosidl_typesupport_introspection_c__Foo_init_function(
  void * message_memory, enum rosidl_runtime_c__message_initialization _init)
{
  // TODO(karsten1987): initializers are not yet implemented for typesupport c
  // see https://github.com/ros2/ros2/issues/397
  (void) _init;
  sample_msg__msg__Foo__init(message_memory);
}

void Foo__rosidl_typesupport_introspection_c__Foo_fini_function(void * message_memory)
{
  sample_msg__msg__Foo__fini(message_memory);
}

static rosidl_typesupport_introspection_c__MessageMember Foo__rosidl_typesupport_introspection_c__Foo_message_member_array[1] = {
  {
    "a",  // name
    rosidl_typesupport_introspection_c__ROS_TYPE_STRING,  // type
    0,  // upper bound of string
    NULL,  // members of sub message
    false,  // is array
    0,  // array size
    false,  // is upper bound
    offsetof(sample_msg__msg__Foo, a),  // bytes offset in struct
    NULL,  // default value
    NULL,  // size() function pointer
    NULL,  // get_const(index) function pointer
    NULL,  // get(index) function pointer
    NULL  // resize(index) function pointer
  }
};

static const rosidl_typesupport_introspection_c__MessageMembers Foo__rosidl_typesupport_introspection_c__Foo_message_members = {
  "sample_msg__msg",  // message namespace
  "Foo",  // message name
  1,  // number of fields
  sizeof(sample_msg__msg__Foo),
  Foo__rosidl_typesupport_introspection_c__Foo_message_member_array,  // message members
  Foo__rosidl_typesupport_introspection_c__Foo_init_function,  // function to initialize message memory (memory has to be allocated)
  Foo__rosidl_typesupport_introspection_c__Foo_fini_function  // function to terminate message instance (will not free memory)
};

// this is not const since it must be initialized on first access
// since C does not allow non-integral compile-time constants
static rosidl_message_type_support_t Foo__rosidl_typesupport_introspection_c__Foo_message_type_support_handle = {
  0,
  &Foo__rosidl_typesupport_introspection_c__Foo_message_members,
  get_message_typesupport_handle_function,
};

ROSIDL_TYPESUPPORT_INTROSPECTION_C_EXPORT_sample_msg
const rosidl_message_type_support_t *
ROSIDL_TYPESUPPORT_INTERFACE__MESSAGE_SYMBOL_NAME(rosidl_typesupport_introspection_c, sample_msg, msg, Foo)() {
  if (!Foo__rosidl_typesupport_introspection_c__Foo_message_type_support_handle.typesupport_identifier) {
    Foo__rosidl_typesupport_introspection_c__Foo_message_type_support_handle.typesupport_identifier =
      rosidl_typesupport_introspection_c__identifier;
  }
  return &Foo__rosidl_typesupport_introspection_c__Foo_message_type_support_handle;
}
#ifdef __cplusplus
}
#endif
