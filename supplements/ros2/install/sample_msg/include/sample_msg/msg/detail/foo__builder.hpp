// generated from rosidl_generator_cpp/resource/idl__builder.hpp.em
// with input from sample_msg:msg/Foo.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__FOO__BUILDER_HPP_
#define SAMPLE_MSG__MSG__DETAIL__FOO__BUILDER_HPP_

#include "sample_msg/msg/detail/foo__struct.hpp"
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <utility>


namespace sample_msg
{

namespace msg
{

namespace builder
{

class Init_Foo_a
{
public:
  Init_Foo_a()
  : msg_(::rosidl_runtime_cpp::MessageInitialization::SKIP)
  {}
  ::sample_msg::msg::Foo a(::sample_msg::msg::Foo::_a_type arg)
  {
    msg_.a = std::move(arg);
    return std::move(msg_);
  }

private:
  ::sample_msg::msg::Foo msg_;
};

}  // namespace builder

}  // namespace msg

template<typename MessageType>
auto build();

template<>
inline
auto build<::sample_msg::msg::Foo>()
{
  return sample_msg::msg::builder::Init_Foo_a();
}

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__FOO__BUILDER_HPP_
