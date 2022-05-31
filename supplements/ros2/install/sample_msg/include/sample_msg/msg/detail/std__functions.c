// generated from rosidl_generator_c/resource/idl__functions.c.em
// with input from sample_msg:msg/Std.idl
// generated code does not contain a copyright notice
#include "sample_msg/msg/detail/std__functions.h"

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>


// Include directives for member types
// Member `l`
#include "rosidl_runtime_c/string_functions.h"
// Member `o`
// Member `limited`
#include "rosidl_runtime_c/primitives_sequence_functions.h"
// Member `q`
#include "std_msgs/msg/detail/bool__functions.h"
// Member `r`
#include "std_msgs/msg/detail/byte__functions.h"
// Member `s`
#include "std_msgs/msg/detail/byte_multi_array__functions.h"
// Member `t`
#include "std_msgs/msg/detail/char__functions.h"
// Member `u`
#include "std_msgs/msg/detail/color_rgba__functions.h"
// Member `w`
#include "std_msgs/msg/detail/empty__functions.h"
// Member `x`
#include "std_msgs/msg/detail/float32__functions.h"
// Member `y`
#include "std_msgs/msg/detail/float32_multi_array__functions.h"
// Member `z`
#include "std_msgs/msg/detail/float64__functions.h"
// Member `aa`
#include "std_msgs/msg/detail/float64_multi_array__functions.h"
// Member `bb`
#include "std_msgs/msg/detail/header__functions.h"
// Member `cc`
#include "std_msgs/msg/detail/int16__functions.h"
// Member `dd`
#include "std_msgs/msg/detail/int16_multi_array__functions.h"
// Member `ee`
#include "std_msgs/msg/detail/int32__functions.h"
// Member `ff`
#include "std_msgs/msg/detail/int32_multi_array__functions.h"
// Member `gg`
#include "std_msgs/msg/detail/int64__functions.h"
// Member `hh`
#include "std_msgs/msg/detail/int64_multi_array__functions.h"
// Member `ii`
#include "std_msgs/msg/detail/int8__functions.h"
// Member `jj`
#include "std_msgs/msg/detail/int8_multi_array__functions.h"
// Member `kk`
#include "std_msgs/msg/detail/multi_array_dimension__functions.h"
// Member `ll`
#include "std_msgs/msg/detail/multi_array_layout__functions.h"
// Member `mm`
#include "std_msgs/msg/detail/string__functions.h"
// Member `oo`
#include "std_msgs/msg/detail/u_int16__functions.h"
// Member `pp`
#include "std_msgs/msg/detail/u_int16_multi_array__functions.h"
// Member `qq`
#include "std_msgs/msg/detail/u_int32__functions.h"
// Member `rr`
#include "std_msgs/msg/detail/u_int32_multi_array__functions.h"
// Member `ss`
#include "std_msgs/msg/detail/u_int64__functions.h"
// Member `tt`
#include "std_msgs/msg/detail/u_int64_multi_array__functions.h"
// Member `uu`
#include "std_msgs/msg/detail/u_int8__functions.h"
// Member `vv`
#include "std_msgs/msg/detail/u_int8_multi_array__functions.h"

bool
sample_msg__msg__Std__init(sample_msg__msg__Std * msg)
{
  if (!msg) {
    return false;
  }
  // a
  // b
  // c
  // d
  // e
  // f
  // g
  // h
  // i
  // j
  // k
  // l
  if (!rosidl_runtime_c__String__init(&msg->l)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // o
  if (!rosidl_runtime_c__int32__Sequence__init(&msg->o, 0)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // p
  // limited
  if (!rosidl_runtime_c__int32__Sequence__init(&msg->limited, 0)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // q
  if (!std_msgs__msg__Bool__init(&msg->q)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // r
  if (!std_msgs__msg__Byte__init(&msg->r)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // s
  if (!std_msgs__msg__ByteMultiArray__init(&msg->s)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // t
  if (!std_msgs__msg__Char__init(&msg->t)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // u
  if (!std_msgs__msg__ColorRGBA__init(&msg->u)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // w
  if (!std_msgs__msg__Empty__init(&msg->w)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // x
  if (!std_msgs__msg__Float32__init(&msg->x)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // y
  if (!std_msgs__msg__Float32MultiArray__init(&msg->y)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // z
  if (!std_msgs__msg__Float64__init(&msg->z)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // aa
  if (!std_msgs__msg__Float64MultiArray__init(&msg->aa)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // bb
  if (!std_msgs__msg__Header__init(&msg->bb)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // cc
  if (!std_msgs__msg__Int16__init(&msg->cc)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // dd
  if (!std_msgs__msg__Int16MultiArray__init(&msg->dd)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // ee
  if (!std_msgs__msg__Int32__init(&msg->ee)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // ff
  if (!std_msgs__msg__Int32MultiArray__init(&msg->ff)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // gg
  if (!std_msgs__msg__Int64__init(&msg->gg)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // hh
  if (!std_msgs__msg__Int64MultiArray__init(&msg->hh)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // ii
  if (!std_msgs__msg__Int8__init(&msg->ii)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // jj
  if (!std_msgs__msg__Int8MultiArray__init(&msg->jj)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // kk
  if (!std_msgs__msg__MultiArrayDimension__init(&msg->kk)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // ll
  if (!std_msgs__msg__MultiArrayLayout__init(&msg->ll)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // mm
  if (!std_msgs__msg__String__init(&msg->mm)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // oo
  if (!std_msgs__msg__UInt16__init(&msg->oo)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // pp
  if (!std_msgs__msg__UInt16MultiArray__init(&msg->pp)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // qq
  if (!std_msgs__msg__UInt32__init(&msg->qq)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // rr
  if (!std_msgs__msg__UInt32MultiArray__init(&msg->rr)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // ss
  if (!std_msgs__msg__UInt64__init(&msg->ss)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // tt
  if (!std_msgs__msg__UInt64MultiArray__init(&msg->tt)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // uu
  if (!std_msgs__msg__UInt8__init(&msg->uu)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // vv
  if (!std_msgs__msg__UInt8MultiArray__init(&msg->vv)) {
    sample_msg__msg__Std__fini(msg);
    return false;
  }
  // ww
  msg->ww = 40l;
  return true;
}

void
sample_msg__msg__Std__fini(sample_msg__msg__Std * msg)
{
  if (!msg) {
    return;
  }
  // a
  // b
  // c
  // d
  // e
  // f
  // g
  // h
  // i
  // j
  // k
  // l
  rosidl_runtime_c__String__fini(&msg->l);
  // o
  rosidl_runtime_c__int32__Sequence__fini(&msg->o);
  // p
  // limited
  rosidl_runtime_c__int32__Sequence__fini(&msg->limited);
  // q
  std_msgs__msg__Bool__fini(&msg->q);
  // r
  std_msgs__msg__Byte__fini(&msg->r);
  // s
  std_msgs__msg__ByteMultiArray__fini(&msg->s);
  // t
  std_msgs__msg__Char__fini(&msg->t);
  // u
  std_msgs__msg__ColorRGBA__fini(&msg->u);
  // w
  std_msgs__msg__Empty__fini(&msg->w);
  // x
  std_msgs__msg__Float32__fini(&msg->x);
  // y
  std_msgs__msg__Float32MultiArray__fini(&msg->y);
  // z
  std_msgs__msg__Float64__fini(&msg->z);
  // aa
  std_msgs__msg__Float64MultiArray__fini(&msg->aa);
  // bb
  std_msgs__msg__Header__fini(&msg->bb);
  // cc
  std_msgs__msg__Int16__fini(&msg->cc);
  // dd
  std_msgs__msg__Int16MultiArray__fini(&msg->dd);
  // ee
  std_msgs__msg__Int32__fini(&msg->ee);
  // ff
  std_msgs__msg__Int32MultiArray__fini(&msg->ff);
  // gg
  std_msgs__msg__Int64__fini(&msg->gg);
  // hh
  std_msgs__msg__Int64MultiArray__fini(&msg->hh);
  // ii
  std_msgs__msg__Int8__fini(&msg->ii);
  // jj
  std_msgs__msg__Int8MultiArray__fini(&msg->jj);
  // kk
  std_msgs__msg__MultiArrayDimension__fini(&msg->kk);
  // ll
  std_msgs__msg__MultiArrayLayout__fini(&msg->ll);
  // mm
  std_msgs__msg__String__fini(&msg->mm);
  // oo
  std_msgs__msg__UInt16__fini(&msg->oo);
  // pp
  std_msgs__msg__UInt16MultiArray__fini(&msg->pp);
  // qq
  std_msgs__msg__UInt32__fini(&msg->qq);
  // rr
  std_msgs__msg__UInt32MultiArray__fini(&msg->rr);
  // ss
  std_msgs__msg__UInt64__fini(&msg->ss);
  // tt
  std_msgs__msg__UInt64MultiArray__fini(&msg->tt);
  // uu
  std_msgs__msg__UInt8__fini(&msg->uu);
  // vv
  std_msgs__msg__UInt8MultiArray__fini(&msg->vv);
  // ww
}

bool
sample_msg__msg__Std__are_equal(const sample_msg__msg__Std * lhs, const sample_msg__msg__Std * rhs)
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
  // d
  if (lhs->d != rhs->d) {
    return false;
  }
  // e
  if (lhs->e != rhs->e) {
    return false;
  }
  // f
  if (lhs->f != rhs->f) {
    return false;
  }
  // g
  if (lhs->g != rhs->g) {
    return false;
  }
  // h
  if (lhs->h != rhs->h) {
    return false;
  }
  // i
  if (lhs->i != rhs->i) {
    return false;
  }
  // j
  if (lhs->j != rhs->j) {
    return false;
  }
  // k
  if (lhs->k != rhs->k) {
    return false;
  }
  // l
  if (!rosidl_runtime_c__String__are_equal(
      &(lhs->l), &(rhs->l)))
  {
    return false;
  }
  // o
  if (!rosidl_runtime_c__int32__Sequence__are_equal(
      &(lhs->o), &(rhs->o)))
  {
    return false;
  }
  // p
  for (size_t i = 0; i < 10; ++i) {
    if (lhs->p[i] != rhs->p[i]) {
      return false;
    }
  }
  // limited
  if (!rosidl_runtime_c__int32__Sequence__are_equal(
      &(lhs->limited), &(rhs->limited)))
  {
    return false;
  }
  // q
  if (!std_msgs__msg__Bool__are_equal(
      &(lhs->q), &(rhs->q)))
  {
    return false;
  }
  // r
  if (!std_msgs__msg__Byte__are_equal(
      &(lhs->r), &(rhs->r)))
  {
    return false;
  }
  // s
  if (!std_msgs__msg__ByteMultiArray__are_equal(
      &(lhs->s), &(rhs->s)))
  {
    return false;
  }
  // t
  if (!std_msgs__msg__Char__are_equal(
      &(lhs->t), &(rhs->t)))
  {
    return false;
  }
  // u
  if (!std_msgs__msg__ColorRGBA__are_equal(
      &(lhs->u), &(rhs->u)))
  {
    return false;
  }
  // w
  if (!std_msgs__msg__Empty__are_equal(
      &(lhs->w), &(rhs->w)))
  {
    return false;
  }
  // x
  if (!std_msgs__msg__Float32__are_equal(
      &(lhs->x), &(rhs->x)))
  {
    return false;
  }
  // y
  if (!std_msgs__msg__Float32MultiArray__are_equal(
      &(lhs->y), &(rhs->y)))
  {
    return false;
  }
  // z
  if (!std_msgs__msg__Float64__are_equal(
      &(lhs->z), &(rhs->z)))
  {
    return false;
  }
  // aa
  if (!std_msgs__msg__Float64MultiArray__are_equal(
      &(lhs->aa), &(rhs->aa)))
  {
    return false;
  }
  // bb
  if (!std_msgs__msg__Header__are_equal(
      &(lhs->bb), &(rhs->bb)))
  {
    return false;
  }
  // cc
  if (!std_msgs__msg__Int16__are_equal(
      &(lhs->cc), &(rhs->cc)))
  {
    return false;
  }
  // dd
  if (!std_msgs__msg__Int16MultiArray__are_equal(
      &(lhs->dd), &(rhs->dd)))
  {
    return false;
  }
  // ee
  if (!std_msgs__msg__Int32__are_equal(
      &(lhs->ee), &(rhs->ee)))
  {
    return false;
  }
  // ff
  if (!std_msgs__msg__Int32MultiArray__are_equal(
      &(lhs->ff), &(rhs->ff)))
  {
    return false;
  }
  // gg
  if (!std_msgs__msg__Int64__are_equal(
      &(lhs->gg), &(rhs->gg)))
  {
    return false;
  }
  // hh
  if (!std_msgs__msg__Int64MultiArray__are_equal(
      &(lhs->hh), &(rhs->hh)))
  {
    return false;
  }
  // ii
  if (!std_msgs__msg__Int8__are_equal(
      &(lhs->ii), &(rhs->ii)))
  {
    return false;
  }
  // jj
  if (!std_msgs__msg__Int8MultiArray__are_equal(
      &(lhs->jj), &(rhs->jj)))
  {
    return false;
  }
  // kk
  if (!std_msgs__msg__MultiArrayDimension__are_equal(
      &(lhs->kk), &(rhs->kk)))
  {
    return false;
  }
  // ll
  if (!std_msgs__msg__MultiArrayLayout__are_equal(
      &(lhs->ll), &(rhs->ll)))
  {
    return false;
  }
  // mm
  if (!std_msgs__msg__String__are_equal(
      &(lhs->mm), &(rhs->mm)))
  {
    return false;
  }
  // oo
  if (!std_msgs__msg__UInt16__are_equal(
      &(lhs->oo), &(rhs->oo)))
  {
    return false;
  }
  // pp
  if (!std_msgs__msg__UInt16MultiArray__are_equal(
      &(lhs->pp), &(rhs->pp)))
  {
    return false;
  }
  // qq
  if (!std_msgs__msg__UInt32__are_equal(
      &(lhs->qq), &(rhs->qq)))
  {
    return false;
  }
  // rr
  if (!std_msgs__msg__UInt32MultiArray__are_equal(
      &(lhs->rr), &(rhs->rr)))
  {
    return false;
  }
  // ss
  if (!std_msgs__msg__UInt64__are_equal(
      &(lhs->ss), &(rhs->ss)))
  {
    return false;
  }
  // tt
  if (!std_msgs__msg__UInt64MultiArray__are_equal(
      &(lhs->tt), &(rhs->tt)))
  {
    return false;
  }
  // uu
  if (!std_msgs__msg__UInt8__are_equal(
      &(lhs->uu), &(rhs->uu)))
  {
    return false;
  }
  // vv
  if (!std_msgs__msg__UInt8MultiArray__are_equal(
      &(lhs->vv), &(rhs->vv)))
  {
    return false;
  }
  // ww
  if (lhs->ww != rhs->ww) {
    return false;
  }
  return true;
}

bool
sample_msg__msg__Std__copy(
  const sample_msg__msg__Std * input,
  sample_msg__msg__Std * output)
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
  // d
  output->d = input->d;
  // e
  output->e = input->e;
  // f
  output->f = input->f;
  // g
  output->g = input->g;
  // h
  output->h = input->h;
  // i
  output->i = input->i;
  // j
  output->j = input->j;
  // k
  output->k = input->k;
  // l
  if (!rosidl_runtime_c__String__copy(
      &(input->l), &(output->l)))
  {
    return false;
  }
  // o
  if (!rosidl_runtime_c__int32__Sequence__copy(
      &(input->o), &(output->o)))
  {
    return false;
  }
  // p
  for (size_t i = 0; i < 10; ++i) {
    output->p[i] = input->p[i];
  }
  // limited
  if (!rosidl_runtime_c__int32__Sequence__copy(
      &(input->limited), &(output->limited)))
  {
    return false;
  }
  // q
  if (!std_msgs__msg__Bool__copy(
      &(input->q), &(output->q)))
  {
    return false;
  }
  // r
  if (!std_msgs__msg__Byte__copy(
      &(input->r), &(output->r)))
  {
    return false;
  }
  // s
  if (!std_msgs__msg__ByteMultiArray__copy(
      &(input->s), &(output->s)))
  {
    return false;
  }
  // t
  if (!std_msgs__msg__Char__copy(
      &(input->t), &(output->t)))
  {
    return false;
  }
  // u
  if (!std_msgs__msg__ColorRGBA__copy(
      &(input->u), &(output->u)))
  {
    return false;
  }
  // w
  if (!std_msgs__msg__Empty__copy(
      &(input->w), &(output->w)))
  {
    return false;
  }
  // x
  if (!std_msgs__msg__Float32__copy(
      &(input->x), &(output->x)))
  {
    return false;
  }
  // y
  if (!std_msgs__msg__Float32MultiArray__copy(
      &(input->y), &(output->y)))
  {
    return false;
  }
  // z
  if (!std_msgs__msg__Float64__copy(
      &(input->z), &(output->z)))
  {
    return false;
  }
  // aa
  if (!std_msgs__msg__Float64MultiArray__copy(
      &(input->aa), &(output->aa)))
  {
    return false;
  }
  // bb
  if (!std_msgs__msg__Header__copy(
      &(input->bb), &(output->bb)))
  {
    return false;
  }
  // cc
  if (!std_msgs__msg__Int16__copy(
      &(input->cc), &(output->cc)))
  {
    return false;
  }
  // dd
  if (!std_msgs__msg__Int16MultiArray__copy(
      &(input->dd), &(output->dd)))
  {
    return false;
  }
  // ee
  if (!std_msgs__msg__Int32__copy(
      &(input->ee), &(output->ee)))
  {
    return false;
  }
  // ff
  if (!std_msgs__msg__Int32MultiArray__copy(
      &(input->ff), &(output->ff)))
  {
    return false;
  }
  // gg
  if (!std_msgs__msg__Int64__copy(
      &(input->gg), &(output->gg)))
  {
    return false;
  }
  // hh
  if (!std_msgs__msg__Int64MultiArray__copy(
      &(input->hh), &(output->hh)))
  {
    return false;
  }
  // ii
  if (!std_msgs__msg__Int8__copy(
      &(input->ii), &(output->ii)))
  {
    return false;
  }
  // jj
  if (!std_msgs__msg__Int8MultiArray__copy(
      &(input->jj), &(output->jj)))
  {
    return false;
  }
  // kk
  if (!std_msgs__msg__MultiArrayDimension__copy(
      &(input->kk), &(output->kk)))
  {
    return false;
  }
  // ll
  if (!std_msgs__msg__MultiArrayLayout__copy(
      &(input->ll), &(output->ll)))
  {
    return false;
  }
  // mm
  if (!std_msgs__msg__String__copy(
      &(input->mm), &(output->mm)))
  {
    return false;
  }
  // oo
  if (!std_msgs__msg__UInt16__copy(
      &(input->oo), &(output->oo)))
  {
    return false;
  }
  // pp
  if (!std_msgs__msg__UInt16MultiArray__copy(
      &(input->pp), &(output->pp)))
  {
    return false;
  }
  // qq
  if (!std_msgs__msg__UInt32__copy(
      &(input->qq), &(output->qq)))
  {
    return false;
  }
  // rr
  if (!std_msgs__msg__UInt32MultiArray__copy(
      &(input->rr), &(output->rr)))
  {
    return false;
  }
  // ss
  if (!std_msgs__msg__UInt64__copy(
      &(input->ss), &(output->ss)))
  {
    return false;
  }
  // tt
  if (!std_msgs__msg__UInt64MultiArray__copy(
      &(input->tt), &(output->tt)))
  {
    return false;
  }
  // uu
  if (!std_msgs__msg__UInt8__copy(
      &(input->uu), &(output->uu)))
  {
    return false;
  }
  // vv
  if (!std_msgs__msg__UInt8MultiArray__copy(
      &(input->vv), &(output->vv)))
  {
    return false;
  }
  // ww
  output->ww = input->ww;
  return true;
}

sample_msg__msg__Std *
sample_msg__msg__Std__create()
{
  sample_msg__msg__Std * msg = (sample_msg__msg__Std *)malloc(sizeof(sample_msg__msg__Std));
  if (!msg) {
    return NULL;
  }
  memset(msg, 0, sizeof(sample_msg__msg__Std));
  bool success = sample_msg__msg__Std__init(msg);
  if (!success) {
    free(msg);
    return NULL;
  }
  return msg;
}

void
sample_msg__msg__Std__destroy(sample_msg__msg__Std * msg)
{
  if (msg) {
    sample_msg__msg__Std__fini(msg);
  }
  free(msg);
}


bool
sample_msg__msg__Std__Sequence__init(sample_msg__msg__Std__Sequence * array, size_t size)
{
  if (!array) {
    return false;
  }
  sample_msg__msg__Std * data = NULL;
  if (size) {
    data = (sample_msg__msg__Std *)calloc(size, sizeof(sample_msg__msg__Std));
    if (!data) {
      return false;
    }
    // initialize all array elements
    size_t i;
    for (i = 0; i < size; ++i) {
      bool success = sample_msg__msg__Std__init(&data[i]);
      if (!success) {
        break;
      }
    }
    if (i < size) {
      // if initialization failed finalize the already initialized array elements
      for (; i > 0; --i) {
        sample_msg__msg__Std__fini(&data[i - 1]);
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
sample_msg__msg__Std__Sequence__fini(sample_msg__msg__Std__Sequence * array)
{
  if (!array) {
    return;
  }
  if (array->data) {
    // ensure that data and capacity values are consistent
    assert(array->capacity > 0);
    // finalize all array elements
    for (size_t i = 0; i < array->capacity; ++i) {
      sample_msg__msg__Std__fini(&array->data[i]);
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

sample_msg__msg__Std__Sequence *
sample_msg__msg__Std__Sequence__create(size_t size)
{
  sample_msg__msg__Std__Sequence * array = (sample_msg__msg__Std__Sequence *)malloc(sizeof(sample_msg__msg__Std__Sequence));
  if (!array) {
    return NULL;
  }
  bool success = sample_msg__msg__Std__Sequence__init(array, size);
  if (!success) {
    free(array);
    return NULL;
  }
  return array;
}

void
sample_msg__msg__Std__Sequence__destroy(sample_msg__msg__Std__Sequence * array)
{
  if (array) {
    sample_msg__msg__Std__Sequence__fini(array);
  }
  free(array);
}

bool
sample_msg__msg__Std__Sequence__are_equal(const sample_msg__msg__Std__Sequence * lhs, const sample_msg__msg__Std__Sequence * rhs)
{
  if (!lhs || !rhs) {
    return false;
  }
  if (lhs->size != rhs->size) {
    return false;
  }
  for (size_t i = 0; i < lhs->size; ++i) {
    if (!sample_msg__msg__Std__are_equal(&(lhs->data[i]), &(rhs->data[i]))) {
      return false;
    }
  }
  return true;
}

bool
sample_msg__msg__Std__Sequence__copy(
  const sample_msg__msg__Std__Sequence * input,
  sample_msg__msg__Std__Sequence * output)
{
  if (!input || !output) {
    return false;
  }
  if (output->capacity < input->size) {
    const size_t allocation_size =
      input->size * sizeof(sample_msg__msg__Std);
    sample_msg__msg__Std * data =
      (sample_msg__msg__Std *)realloc(output->data, allocation_size);
    if (!data) {
      return false;
    }
    for (size_t i = output->capacity; i < input->size; ++i) {
      if (!sample_msg__msg__Std__init(&data[i])) {
        /* free currently allocated and return false */
        for (; i-- > output->capacity; ) {
          sample_msg__msg__Std__fini(&data[i]);
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
    if (!sample_msg__msg__Std__copy(
        &(input->data[i]), &(output->data[i])))
    {
      return false;
    }
  }
  return true;
}
