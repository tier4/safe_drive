// generated from rosidl_generator_cpp/resource/idl__builder.hpp.em
// with input from sample_msg:srv/AddThreeInts.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__SRV__DETAIL__ADD_THREE_INTS__BUILDER_HPP_
#define SAMPLE_MSG__SRV__DETAIL__ADD_THREE_INTS__BUILDER_HPP_

#include "sample_msg/srv/detail/add_three_ints__struct.hpp"
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <utility>


namespace sample_msg
{

namespace srv
{

namespace builder
{

class Init_AddThreeInts_Request_c
{
public:
  explicit Init_AddThreeInts_Request_c(::sample_msg::srv::AddThreeInts_Request & msg)
  : msg_(msg)
  {}
  ::sample_msg::srv::AddThreeInts_Request c(::sample_msg::srv::AddThreeInts_Request::_c_type arg)
  {
    msg_.c = std::move(arg);
    return std::move(msg_);
  }

private:
  ::sample_msg::srv::AddThreeInts_Request msg_;
};

class Init_AddThreeInts_Request_b
{
public:
  explicit Init_AddThreeInts_Request_b(::sample_msg::srv::AddThreeInts_Request & msg)
  : msg_(msg)
  {}
  Init_AddThreeInts_Request_c b(::sample_msg::srv::AddThreeInts_Request::_b_type arg)
  {
    msg_.b = std::move(arg);
    return Init_AddThreeInts_Request_c(msg_);
  }

private:
  ::sample_msg::srv::AddThreeInts_Request msg_;
};

class Init_AddThreeInts_Request_a
{
public:
  Init_AddThreeInts_Request_a()
  : msg_(::rosidl_runtime_cpp::MessageInitialization::SKIP)
  {}
  Init_AddThreeInts_Request_b a(::sample_msg::srv::AddThreeInts_Request::_a_type arg)
  {
    msg_.a = std::move(arg);
    return Init_AddThreeInts_Request_b(msg_);
  }

private:
  ::sample_msg::srv::AddThreeInts_Request msg_;
};

}  // namespace builder

}  // namespace srv

template<typename MessageType>
auto build();

template<>
inline
auto build<::sample_msg::srv::AddThreeInts_Request>()
{
  return sample_msg::srv::builder::Init_AddThreeInts_Request_a();
}

}  // namespace sample_msg


namespace sample_msg
{

namespace srv
{

namespace builder
{

class Init_AddThreeInts_Response_sum
{
public:
  Init_AddThreeInts_Response_sum()
  : msg_(::rosidl_runtime_cpp::MessageInitialization::SKIP)
  {}
  ::sample_msg::srv::AddThreeInts_Response sum(::sample_msg::srv::AddThreeInts_Response::_sum_type arg)
  {
    msg_.sum = std::move(arg);
    return std::move(msg_);
  }

private:
  ::sample_msg::srv::AddThreeInts_Response msg_;
};

}  // namespace builder

}  // namespace srv

template<typename MessageType>
auto build();

template<>
inline
auto build<::sample_msg::srv::AddThreeInts_Response>()
{
  return sample_msg::srv::builder::Init_AddThreeInts_Response_sum();
}

}  // namespace sample_msg

#endif  // SAMPLE_MSG__SRV__DETAIL__ADD_THREE_INTS__BUILDER_HPP_
