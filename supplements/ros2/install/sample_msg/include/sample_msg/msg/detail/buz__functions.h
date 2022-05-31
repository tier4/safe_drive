// generated from rosidl_generator_c/resource/idl__functions.h.em
// with input from sample_msg:msg/Buz.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__BUZ__FUNCTIONS_H_
#define SAMPLE_MSG__MSG__DETAIL__BUZ__FUNCTIONS_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdbool.h>
#include <stdlib.h>

#include "rosidl_runtime_c/visibility_control.h"
#include "sample_msg/msg/rosidl_generator_c__visibility_control.h"

#include "sample_msg/msg/detail/buz__struct.h"

/// Initialize msg/Buz message.
/**
 * If the init function is called twice for the same message without
 * calling fini inbetween previously allocated memory will be leaked.
 * \param[in,out] msg The previously allocated message pointer.
 * Fields without a default value will not be initialized by this function.
 * You might want to call memset(msg, 0, sizeof(
 * sample_msg__msg__Buz
 * )) before or use
 * sample_msg__msg__Buz__create()
 * to allocate and initialize the message.
 * \return true if initialization was successful, otherwise false
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Buz__init(sample_msg__msg__Buz * msg);

/// Finalize msg/Buz message.
/**
 * \param[in,out] msg The allocated message pointer.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
void
sample_msg__msg__Buz__fini(sample_msg__msg__Buz * msg);

/// Create msg/Buz message.
/**
 * It allocates the memory for the message, sets the memory to zero, and
 * calls
 * sample_msg__msg__Buz__init().
 * \return The pointer to the initialized message if successful,
 * otherwise NULL
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
sample_msg__msg__Buz *
sample_msg__msg__Buz__create();

/// Destroy msg/Buz message.
/**
 * It calls
 * sample_msg__msg__Buz__fini()
 * and frees the memory of the message.
 * \param[in,out] msg The allocated message pointer.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
void
sample_msg__msg__Buz__destroy(sample_msg__msg__Buz * msg);

/// Check for msg/Buz message equality.
/**
 * \param[in] lhs The message on the left hand size of the equality operator.
 * \param[in] rhs The message on the right hand size of the equality operator.
 * \return true if messages are equal, otherwise false.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Buz__are_equal(const sample_msg__msg__Buz * lhs, const sample_msg__msg__Buz * rhs);

/// Copy a msg/Buz message.
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
sample_msg__msg__Buz__copy(
  const sample_msg__msg__Buz * input,
  sample_msg__msg__Buz * output);

/// Initialize array of msg/Buz messages.
/**
 * It allocates the memory for the number of elements and calls
 * sample_msg__msg__Buz__init()
 * for each element of the array.
 * \param[in,out] array The allocated array pointer.
 * \param[in] size The size / capacity of the array.
 * \return true if initialization was successful, otherwise false
 * If the array pointer is valid and the size is zero it is guaranteed
 # to return true.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Buz__Sequence__init(sample_msg__msg__Buz__Sequence * array, size_t size);

/// Finalize array of msg/Buz messages.
/**
 * It calls
 * sample_msg__msg__Buz__fini()
 * for each element of the array and frees the memory for the number of
 * elements.
 * \param[in,out] array The initialized array pointer.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
void
sample_msg__msg__Buz__Sequence__fini(sample_msg__msg__Buz__Sequence * array);

/// Create array of msg/Buz messages.
/**
 * It allocates the memory for the array and calls
 * sample_msg__msg__Buz__Sequence__init().
 * \param[in] size The size / capacity of the array.
 * \return The pointer to the initialized array if successful, otherwise NULL
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
sample_msg__msg__Buz__Sequence *
sample_msg__msg__Buz__Sequence__create(size_t size);

/// Destroy array of msg/Buz messages.
/**
 * It calls
 * sample_msg__msg__Buz__Sequence__fini()
 * on the array,
 * and frees the memory of the array.
 * \param[in,out] array The initialized array pointer.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
void
sample_msg__msg__Buz__Sequence__destroy(sample_msg__msg__Buz__Sequence * array);

/// Check for msg/Buz message array equality.
/**
 * \param[in] lhs The message array on the left hand size of the equality operator.
 * \param[in] rhs The message array on the right hand size of the equality operator.
 * \return true if message arrays are equal in size and content, otherwise false.
 */
ROSIDL_GENERATOR_C_PUBLIC_sample_msg
bool
sample_msg__msg__Buz__Sequence__are_equal(const sample_msg__msg__Buz__Sequence * lhs, const sample_msg__msg__Buz__Sequence * rhs);

/// Copy an array of msg/Buz messages.
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
sample_msg__msg__Buz__Sequence__copy(
  const sample_msg__msg__Buz__Sequence * input,
  sample_msg__msg__Buz__Sequence * output);

#ifdef __cplusplus
}
#endif

#endif  // SAMPLE_MSG__MSG__DETAIL__BUZ__FUNCTIONS_H_
