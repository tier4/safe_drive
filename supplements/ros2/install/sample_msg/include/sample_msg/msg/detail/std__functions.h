// generated from rosidl_generator_c/resource/idl__functions.h.em
// with input from sample_msg:msg/Std.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__STD__FUNCTIONS_H_
#define SAMPLE_MSG__MSG__DETAIL__STD__FUNCTIONS_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdbool.h>
#include <stdlib.h>

#include "rosidl_runtime_c/visibility_control.h"
#include "sample_msg/msg/rosidl_generator_c__visibility_control.h"

#include "sample_msg/msg/detail/std__struct.h"

/// Initialize msg/Std message.
/**
 * If the init function is called twice for the same message without
 * calling fini inbetween previously allocated memory will be leaked.
 * \param[in,out] msg The previously allocated message pointer.
 * Fields without a default value will not be initialized by this function.
 * You might want to call memset(msg, 0, sizeof(
 * sample_msg__msg__Std
 * )) before or use
 * sample_msg__msg__Std__create()
 * to allocate and initialize the message.
 * \return true if initialization was successful, otherwise false
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Std__init(sample_msg__msg__Std * msg);

/// Finalize msg/Std message.
/**
 * \param[in,out] msg The allocated message pointer.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
void
sample_msg__msg__Std__fini(sample_msg__msg__Std * msg);

/// Create msg/Std message.
/**
 * It allocates the memory for the message, sets the memory to zero, and
 * calls
 * sample_msg__msg__Std__init().
 * \return The pointer to the initialized message if successful,
 * otherwise NULL
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
sample_msg__msg__Std *
sample_msg__msg__Std__create();

/// Destroy msg/Std message.
/**
 * It calls
 * sample_msg__msg__Std__fini()
 * and frees the memory of the message.
 * \param[in,out] msg The allocated message pointer.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
void
sample_msg__msg__Std__destroy(sample_msg__msg__Std * msg);

/// Check for msg/Std message equality.
/**
 * \param[in] lhs The message on the left hand size of the equality operator.
 * \param[in] rhs The message on the right hand size of the equality operator.
 * \return true if messages are equal, otherwise false.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Std__are_equal(const sample_msg__msg__Std * lhs, const sample_msg__msg__Std * rhs);

/// Copy a msg/Std message.
/**
 * This functions performs a deep copy, as opposed to the shallow copy that
 * plain assignment yields.
 *
 * \param[in] input The source message pointer.
 * \param[out] output The target message pointer, which must
 *   have been initialized before calling this function.
 * \return true if successful, or false if either pointer is null
 *   or memory allocation fails.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Std__copy(
  const sample_msg__msg__Std * input,
  sample_msg__msg__Std * output);

/// Initialize array of msg/Std messages.
/**
 * It allocates the memory for the number of elements and calls
 * sample_msg__msg__Std__init()
 * for each element of the array.
 * \param[in,out] array The allocated array pointer.
 * \param[in] size The size / capacity of the array.
 * \return true if initialization was successful, otherwise false
 * If the array pointer is valid and the size is zero it is guaranteed
 # to return true.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Std__Sequence__init(sample_msg__msg__Std__Sequence * array, size_t size);

/// Finalize array of msg/Std messages.
/**
 * It calls
 * sample_msg__msg__Std__fini()
 * for each element of the array and frees the memory for the number of
 * elements.
 * \param[in,out] array The initialized array pointer.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
void
sample_msg__msg__Std__Sequence__fini(sample_msg__msg__Std__Sequence * array);

/// Create array of msg/Std messages.
/**
 * It allocates the memory for the array and calls
 * sample_msg__msg__Std__Sequence__init().
 * \param[in] size The size / capacity of the array.
 * \return The pointer to the initialized array if successful, otherwise NULL
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
sample_msg__msg__Std__Sequence *
sample_msg__msg__Std__Sequence__create(size_t size);

/// Destroy array of msg/Std messages.
/**
 * It calls
 * sample_msg__msg__Std__Sequence__fini()
 * on the array,
 * and frees the memory of the array.
 * \param[in,out] array The initialized array pointer.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
void
sample_msg__msg__Std__Sequence__destroy(sample_msg__msg__Std__Sequence * array);

/// Check for msg/Std message array equality.
/**
 * \param[in] lhs The message array on the left hand size of the equality operator.
 * \param[in] rhs The message array on the right hand size of the equality operator.
 * \return true if message arrays are equal in size and content, otherwise false.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Std__Sequence__are_equal(const sample_msg__msg__Std__Sequence * lhs, const sample_msg__msg__Std__Sequence * rhs);

/// Copy an array of msg/Std messages.
/**
 * This functions performs a deep copy, as opposed to the shallow copy that
 * plain assignment yields.
 *
 * \param[in] input The source array pointer.
 * \param[out] output The target array pointer, which must
 *   have been initialized before calling this function.
 * \return true if successful, or false if either pointer
 *   is null or memory allocation fails.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Std__Sequence__copy(
  const sample_msg__msg__Std__Sequence * input,
  sample_msg__msg__Std__Sequence * output);

#ifdef __cplusplus
}
#endif

#endif  // SAMPLE_MSG__MSG__DETAIL__STD__FUNCTIONS_H_
