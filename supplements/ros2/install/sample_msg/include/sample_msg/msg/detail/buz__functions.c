// generated from rosidl_generator_c/resource/idl__functions.c.em
// with input from sample_msg:msg/Buz.idl
// generated code does not contain a copyright notice
#include "sample_msg/msg/detail/buz__functions.h"

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>


// Include directives for member types
// Member `c`
#include "rosidl_runtime_c/string_functions.h"

bool
sample_msg__msg__Buz__init(sample_msg__msg__Buz * msg)
{
  if (!msg) {
    return false;
  }
  // c
  if (!rosidl_runtime_c__String__init(&msg->c)) {
    sample_msg__msg__Buz__fini(msg);
    return false;
  }
  return true;
}

void
sample_msg__msg__Buz__fini(sample_msg__msg__Buz * msg)
{
  if (!msg) {
    return;
  }
  // c
  rosidl_runtime_c__String__fini(&msg->c);
}

bool
sample_msg__msg__Buz__are_equal(const sample_msg__msg__Buz * lhs, const sample_msg__msg__Buz * rhs)
{
  if (!lhs || !rhs) {
    return false;
  }
  // c
  if (!rosidl_runtime_c__String__are_equal(
      &(lhs->c), &(rhs->c)))
  {
    return false;
  }
  return true;
}

bool
sample_msg__msg__Buz__copy(
  const sample_msg__msg__Buz * input,
  sample_msg__msg__Buz * output)
{
  if (!input || !output) {
    return false;
  }
  // c
  if (!rosidl_runtime_c__String__copy(
      &(input->c), &(output->c)))
  {
    return false;
  }
  return true;
}

sample_msg__msg__Buz *
sample_msg__msg__Buz__create()
{
  sample_msg__msg__Buz * msg = (sample_msg__msg__Buz *)malloc(sizeof(sample_msg__msg__Buz));
  if (!msg) {
    return NULL;
  }
  memset(msg, 0, sizeof(sample_msg__msg__Buz));
  bool success = sample_msg__msg__Buz__init(msg);
  if (!success) {
    free(msg);
    return NULL;
  }
  return msg;
}

void
sample_msg__msg__Buz__destroy(sample_msg__msg__Buz * msg)
{
  if (msg) {
    sample_msg__msg__Buz__fini(msg);
  }
  free(msg);
}


bool
sample_msg__msg__Buz__Sequence__init(sample_msg__msg__Buz__Sequence * array, size_t size)
{
  if (!array) {
    return false;
  }
  sample_msg__msg__Buz * data = NULL;
  if (size) {
    data = (sample_msg__msg__Buz *)calloc(size, sizeof(sample_msg__msg__Buz));
    if (!data) {
      return false;
    }
    // initialize all array elements
    size_t i;
    for (i = 0; i < size; ++i) {
      bool success = sample_msg__msg__Buz__init(&data[i]);
      if (!success) {
        break;
      }
    }
    if (i < size) {
      // if initialization failed finalize the already initialized array elements
      for (; i > 0; --i) {
        sample_msg__msg__Buz__fini(&data[i - 1]);
      }
      free(data);
      return false;
    }
  }
  array->data = data;
  array->size = size;
  array->capacity = size;
  return true;
}

void
sample_msg__msg__Buz__Sequence__fini(sample_msg__msg__Buz__Sequence * array)
{
  if (!array) {
    return;
  }
  if (array->data) {
    // ensure that data and capacity values are consistent
    assert(array->capacity > 0);
    // finalize all array elements
    for (size_t i = 0; i < array->capacity; ++i) {
      sample_msg__msg__Buz__fini(&array->data[i]);
    }
    free(array->data);
    array->data = NULL;
    array->size = 0;
    array->capacity = 0;
  } else {
    // ensure that data, size, and capacity values are consistent
    assert(0 == array->size);
    assert(0 == array->capacity);
  }
}

sample_msg__msg__Buz__Sequence *
sample_msg__msg__Buz__Sequence__create(size_t size)
{
  sample_msg__msg__Buz__Sequence * array = (sample_msg__msg__Buz__Sequence *)malloc(sizeof(sample_msg__msg__Buz__Sequence));
  if (!array) {
    return NULL;
  }
  bool success = sample_msg__msg__Buz__Sequence__init(array, size);
  if (!success) {
    free(array);
    return NULL;
  }
  return array;
}

void
sample_msg__msg__Buz__Sequence__destroy(sample_msg__msg__Buz__Sequence * array)
{
  if (array) {
    sample_msg__msg__Buz__Sequence__fini(array);
  }
  free(array);
}

bool
sample_msg__msg__Buz__Sequence__are_equal(const sample_msg__msg__Buz__Sequence * lhs, const sample_msg__msg__Buz__Sequence * rhs)
{
  if (!lhs || !rhs) {
    return false;
  }
  if (lhs->size != rhs->size) {
    return false;
  }
  for (size_t i = 0; i < lhs->size; ++i) {
    if (!sample_msg__msg__Buz__are_equal(&(lhs->data[i]), &(rhs->data[i]))) {
      return false;
    }
  }
  return true;
}

bool
sample_msg__msg__Buz__Sequence__copy(
  const sample_msg__msg__Buz__Sequence * input,
  sample_msg__msg__Buz__Sequence * output)
{
  if (!input || !output) {
    return false;
  }
  if (output->capacity < input->size) {
    const size_t allocation_size =
      input->size * sizeof(sample_msg__msg__Buz);
    sample_msg__msg__Buz * data =
      (sample_msg__msg__Buz *)realloc(output->data, allocation_size);
    if (!data) {
      return false;
    }
    for (size_t i = output->capacity; i < input->size; ++i) {
      if (!sample_msg__msg__Buz__init(&data[i])) {
        /* free currently allocated and return false */
        for (; i-- > output->capacity; ) {
          sample_msg__msg__Buz__fini(&data[i]);
        }
        free(data);
        return false;
      }
    }
    output->data = data;
    output->capacity = input->size;
  }
  output->size = input->size;
  for (size_t i = 0; i < input->size; ++i) {
    if (!sample_msg__msg__Buz__copy(
        &(input->data[i]), &(output->data[i])))
    {
      return false;
    }
  }
  return true;
}
