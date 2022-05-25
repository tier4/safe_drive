// generated from rosidl_generator_cpp/resource/idl__builder.hpp.em
// with input from sample_msg:msg/Num.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__NUM__BUILDER_HPP_
#define SAMPLE_MSG__MSG__DETAIL__NUM__BUILDER_HPP_

#include "sample_msg/msg/detail/num__struct.hpp"
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <utility>


namespace sample_msg
{

namespace msg
{

namespace builder
{

class Init_Num_num
{
public:
  Init_Num_num()
  : msg_(::rosidl_runtime_cpp::MessageInitialization::SKIP)
  {}
  ::sample_msg::msg::Num num(::sample_msg::msg::Num::_num_type arg)
  {
    msg_.num = std::move(arg);
    return std::move(msg_);
  }

private:
  ::sample_msg::msg::Num msg_;
};

}  // namespace builder

}  // namespace msg

template<typename MessageType>
auto build();

template<>
inline
auto build<::sample_msg::msg::Num>()
{
  return sample_msg::msg::builder::Init_Num_num();
}

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__NUM__BUILDER_HPP_
