// generated from rosidl_generator_cpp/resource/idl__builder.hpp.em
// with input from sample_msg:msg/Buz.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__BUZ__BUILDER_HPP_
#define SAMPLE_MSG__MSG__DETAIL__BUZ__BUILDER_HPP_

#include "sample_msg/msg/detail/buz__struct.hpp"
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <utility>


namespace sample_msg
{

namespace msg
{

namespace builder
{

class Init_Buz_c
{
public:
  Init_Buz_c()
  : msg_(::rosidl_runtime_cpp::MessageInitialization::SKIP)
  {}
  ::sample_msg::msg::Buz c(::sample_msg::msg::Buz::_c_type arg)
  {
    msg_.c = std::move(arg);
    return std::move(msg_);
  }

private:
  ::sample_msg::msg::Buz msg_;
};

}  // namespace builder

}  // namespace msg

template<typename MessageType>
auto build();

template<>
inline
auto build<::sample_msg::msg::Buz>()
{
  return sample_msg::msg::builder::Init_Buz_c();
}

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__BUZ__BUILDER_HPP_
