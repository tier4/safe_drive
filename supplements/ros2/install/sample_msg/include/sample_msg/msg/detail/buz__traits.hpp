// generated from rosidl_generator_cpp/resource/idl__traits.hpp.em
// with input from sample_msg:msg/Buz.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__BUZ__TRAITS_HPP_
#define SAMPLE_MSG__MSG__DETAIL__BUZ__TRAITS_HPP_

#include "sample_msg/msg/detail/buz__struct.hpp"
#include <stdint.h>
#include <rosidl_runtime_cpp/traits.hpp>
#include <sstream>
#include <string>
#include <type_traits>

namespace rosidl_generator_traits
{

inline void to_yaml(
  const sample_msg::msg::Buz & msg,
  std::ostream & out, size_t indentation = 0)
{
  // member: c
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "c: ";
    value_to_yaml(msg.c, out);
    out << "\n";
  }
}  // NOLINT(readability/fn_size)

inline std::string to_yaml(const sample_msg::msg::Buz & msg)
{
  std::ostringstream out;
  to_yaml(msg, out);
  return out.str();
}

template<>
inline const char * data_type<sample_msg::msg::Buz>()
{
  return "sample_msg::msg::Buz";
}

template<>
inline const char * name<sample_msg::msg::Buz>()
{
  return "sample_msg/msg/Buz";
}

template<>
struct has_fixed_size<sample_msg::msg::Buz>
  : std::integral_constant<bool, false> {};

template<>
struct has_bounded_size<sample_msg::msg::Buz>
  : std::integral_constant<bool, false> {};

template<>
struct is_message<sample_msg::msg::Buz>
  : std::true_type {};

}  // namespace rosidl_generator_traits

#endif  // SAMPLE_MSG__MSG__DETAIL__BUZ__TRAITS_HPP_
