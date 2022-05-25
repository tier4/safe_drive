// generated from rosidl_generator_c/resource/idl__functions.c.em
// with input from sample_msg:srv/AddThreeInts.idl
// generated code does not contain a copyright notice
#include "sample_msg/srv/detail/add_three_ints__functions.h"

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

bool
sample_msg__srv__AddThreeInts_Request__init(sample_msg__srv__AddThreeInts_Request * msg)
{
  if (!msg) {
    return false;
  }
  // a
  // b
  // c
  return true;
}

void
sample_msg__srv__AddThreeInts_Request__fini(sample_msg__srv__AddThreeInts_Request * msg)
{
  if (!msg) {
    return;
  }
  // a
  // b
  // c
}

bool
sample_msg__srv__AddThreeInts_Request__are_equal(const sample_msg__srv__AddThreeInts_Request * lhs, const sample_msg__srv__AddThreeInts_Request * rhs)
{
  if (!lhs || !rhs) {
    return false;
  }
  // a
  if (lhs->a != rhs->a) {
    return false;
  }
  // b
  if (lhs->b != rhs->b) {
    return false;
  }
  // c
  if (lhs->c != rhs->c) {
    return false;
  }
  return true;
}

bool
sample_msg__srv__AddThreeInts_Request__copy(
  const sample_msg__srv__AddThreeInts_Request * input,
  sample_msg__srv__AddThreeInts_Request * output)
{
  if (!input || !output) {
    return false;
  }
  // a
  output->a = input->a;
  // b
  output->b = input->b;
  // c
  output->c = input->c;
  return true;
}

sample_msg__srv__AddThreeInts_Request *
sample_msg__srv__AddThreeInts_Request__create()
{
  sample_msg__srv__AddThreeInts_Request * msg = (sample_msg__srv__AddThreeInts_Request *)malloc(sizeof(sample_msg__srv__AddThreeInts_Request));
  if (!msg) {
    return NULL;
  }
  memset(msg, 0, sizeof(sample_msg__srv__AddThreeInts_Request));
  bool success = sample_msg__srv__AddThreeInts_Request__init(msg);
  if (!success) {
    free(msg);
    return NULL;
  }
  return msg;
}

void
sample_msg__srv__AddThreeInts_Request__destroy(sample_msg__srv__AddThreeInts_Request * msg)
{
  if (msg) {
    sample_msg__srv__AddThreeInts_Request__fini(msg);
  }
  free(msg);
}


bool
sample_msg__srv__AddThreeInts_Request__Sequence__init(sample_msg__srv__AddThreeInts_Request__Sequence * array, size_t size)
{
  if (!array) {
    return false;
  }
  sample_msg__srv__AddThreeInts_Request * data = NULL;
  if (size) {
    data = (sample_msg__srv__AddThreeInts_Request *)calloc(size, sizeof(sample_msg__srv__AddThreeInts_Request));
    if (!data) {
      return false;
    }
    // initialize all array elements
    size_t i;
    for (i = 0; i < size; ++i) {
      bool success = sample_msg__srv__AddThreeInts_Request__init(&data[i]);
      if (!success) {
        break;
      }
    }
    if (i < size) {
      // if initialization failed finalize the already initialized array elements
      for (; i > 0; --i) {
        sample_msg__srv__AddThreeInts_Request__fini(&data[i - 1]);
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
sample_msg__srv__AddThreeInts_Request__Sequence__fini(sample_msg__srv__AddThreeInts_Request__Sequence * array)
{
  if (!array) {
    return;
  }
  if (array->data) {
    // ensure that data and capacity values are consistent
    assert(array->capacity > 0);
    // finalize all array elements
    for (size_t i = 0; i < array->capacity; ++i) {
      sample_msg__srv__AddThreeInts_Request__fini(&array->data[i]);
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

sample_msg__srv__AddThreeInts_Request__Sequence *
sample_msg__srv__AddThreeInts_Request__Sequence__create(size_t size)
{
  sample_msg__srv__AddThreeInts_Request__Sequence * array = (sample_msg__srv__AddThreeInts_Request__Sequence *)malloc(sizeof(sample_msg__srv__AddThreeInts_Request__Sequence));
  if (!array) {
    return NULL;
  }
  bool success = sample_msg__srv__AddThreeInts_Request__Sequence__init(array, size);
  if (!success) {
    free(array);
    return NULL;
  }
  return array;
}

void
sample_msg__srv__AddThreeInts_Request__Sequence__destroy(sample_msg__srv__AddThreeInts_Request__Sequence * array)
{
  if (array) {
    sample_msg__srv__AddThreeInts_Request__Sequence__fini(array);
  }
  free(array);
}

bool
sample_msg__srv__AddThreeInts_Request__Sequence__are_equal(const sample_msg__srv__AddThreeInts_Request__Sequence * lhs, const sample_msg__srv__AddThreeInts_Request__Sequence * rhs)
{
  if (!lhs || !rhs) {
    return false;
  }
  if (lhs->size != rhs->size) {
    return false;
  }
  for (size_t i = 0; i < lhs->size; ++i) {
    if (!sample_msg__srv__AddThreeInts_Request__are_equal(&(lhs->data[i]), &(rhs->data[i]))) {
      return false;
    }
  }
  return true;
}

bool
sample_msg__srv__AddThreeInts_Request__Sequence__copy(
  const sample_msg__srv__AddThreeInts_Request__Sequence * input,
  sample_msg__srv__AddThreeInts_Request__Sequence * output)
{
  if (!input || !output) {
    return false;
  }
  if (output->capacity < input->size) {
    const size_t allocation_size =
      input->size * sizeof(sample_msg__srv__AddThreeInts_Request);
    sample_msg__srv__AddThreeInts_Request * data =
      (sample_msg__srv__AddThreeInts_Request *)realloc(output->data, allocation_size);
    if (!data) {
      return false;
    }
    for (size_t i = output->capacity; i < input->size; ++i) {
      if (!sample_msg__srv__AddThreeInts_Request__init(&data[i])) {
        /* free currently allocated and return false */
        for (; i-- > output->capacity; ) {
          sample_msg__srv__AddThreeInts_Request__fini(&data[i]);
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
    if (!sample_msg__srv__AddThreeInts_Request__copy(
        &(input->data[i]), &(output->data[i])))
    {
      return false;
    }
  }
  return true;
}


bool
sample_msg__srv__AddThreeInts_Response__init(sample_msg__srv__AddThreeInts_Response * msg)
{
  if (!msg) {
    return false;
  }
  // sum
  return true;
}

void
sample_msg__srv__AddThreeInts_Response__fini(sample_msg__srv__AddThreeInts_Response * msg)
{
  if (!msg) {
    return;
  }
  // sum
}

bool
sample_msg__srv__AddThreeInts_Response__are_equal(const sample_msg__srv__AddThreeInts_Response * lhs, const sample_msg__srv__AddThreeInts_Response * rhs)
{
  if (!lhs || !rhs) {
    return false;
  }
  // sum
  if (lhs->sum != rhs->sum) {
    return false;
  }
  return true;
}

bool
sample_msg__srv__AddThreeInts_Response__copy(
  const sample_msg__srv__AddThreeInts_Response * input,
  sample_msg__srv__AddThreeInts_Response * output)
{
  if (!input || !output) {
    return false;
  }
  // sum
  output->sum = input->sum;
  return true;
}

sample_msg__srv__AddThreeInts_Response *
sample_msg__srv__AddThreeInts_Response__create()
{
  sample_msg__srv__AddThreeInts_Response * msg = (sample_msg__srv__AddThreeInts_Response *)malloc(sizeof(sample_msg__srv__AddThreeInts_Response));
  if (!msg) {
    return NULL;
  }
  memset(msg, 0, sizeof(sample_msg__srv__AddThreeInts_Response));
  bool success = sample_msg__srv__AddThreeInts_Response__init(msg);
  if (!success) {
    free(msg);
    return NULL;
  }
  return msg;
}

void
sample_msg__srv__AddThreeInts_Response__destroy(sample_msg__srv__AddThreeInts_Response * msg)
{
  if (msg) {
    sample_msg__srv__AddThreeInts_Response__fini(msg);
  }
  free(msg);
}


bool
sample_msg__srv__AddThreeInts_Response__Sequence__init(sample_msg__srv__AddThreeInts_Response__Sequence * array, size_t size)
{
  if (!array) {
    return false;
  }
  sample_msg__srv__AddThreeInts_Response * data = NULL;
  if (size) {
    data = (sample_msg__srv__AddThreeInts_Response *)calloc(size, sizeof(sample_msg__srv__AddThreeInts_Response));
    if (!data) {
      return false;
    }
    // initialize all array elements
    size_t i;
    for (i = 0; i < size; ++i) {
      bool success = sample_msg__srv__AddThreeInts_Response__init(&data[i]);
      if (!success) {
        break;
      }
    }
    if (i < size) {
      // if initialization failed finalize the already initialized array elements
      for (; i > 0; --i) {
        sample_msg__srv__AddThreeInts_Response__fini(&data[i - 1]);
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
sample_msg__srv__AddThreeInts_Response__Sequence__fini(sample_msg__srv__AddThreeInts_Response__Sequence * array)
{
  if (!array) {
    return;
  }
  if (array->data) {
    // ensure that data and capacity values are consistent
    assert(array->capacity > 0);
    // finalize all array elements
    for (size_t i = 0; i < array->capacity; ++i) {
      sample_msg__srv__AddThreeInts_Response__fini(&array->data[i]);
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

sample_msg__srv__AddThreeInts_Response__Sequence *
sample_msg__srv__AddThreeInts_Response__Sequence__create(size_t size)
{
  sample_msg__srv__AddThreeInts_Response__Sequence * array = (sample_msg__srv__AddThreeInts_Response__Sequence *)malloc(sizeof(sample_msg__srv__AddThreeInts_Response__Sequence));
  if (!array) {
    return NULL;
  }
  bool success = sample_msg__srv__AddThreeInts_Response__Sequence__init(array, size);
  if (!success) {
    free(array);
    return NULL;
  }
  return array;
}

void
sample_msg__srv__AddThreeInts_Response__Sequence__destroy(sample_msg__srv__AddThreeInts_Response__Sequence * array)
{
  if (array) {
    sample_msg__srv__AddThreeInts_Response__Sequence__fini(array);
  }
  free(array);
}

bool
sample_msg__srv__AddThreeInts_Response__Sequence__are_equal(const sample_msg__srv__AddThreeInts_Response__Sequence * lhs, const sample_msg__srv__AddThreeInts_Response__Sequence * rhs)
{
  if (!lhs || !rhs) {
    return false;
  }
  if (lhs->size != rhs->size) {
    return false;
  }
  for (size_t i = 0; i < lhs->size; ++i) {
    if (!sample_msg__srv__AddThreeInts_Response__are_equal(&(lhs->data[i]), &(rhs->data[i]))) {
      return false;
    }
  }
  return true;
}

bool
sample_msg__srv__AddThreeInts_Response__Sequence__copy(
  const sample_msg__srv__AddThreeInts_Response__Sequence * input,
  sample_msg__srv__AddThreeInts_Response__Sequence * output)
{
  if (!input || !output) {
    return false;
  }
  if (output->capacity < input->size) {
    const size_t allocation_size =
      input->size * sizeof(sample_msg__srv__AddThreeInts_Response);
    sample_msg__srv__AddThreeInts_Response * data =
      (sample_msg__srv__AddThreeInts_Response *)realloc(output->data, allocation_size);
    if (!data) {
      return false;
    }
    for (size_t i = output->capacity; i < input->size; ++i) {
      if (!sample_msg__srv__AddThreeInts_Response__init(&data[i])) {
        /* free currently allocated and return false */
        for (; i-- > output->capacity; ) {
          sample_msg__srv__AddThreeInts_Response__fini(&data[i]);
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
    if (!sample_msg__srv__AddThreeInts_Response__copy(
        &(input->data[i]), &(output->data[i])))
    {
      return false;
    }
  }
  return true;
}
