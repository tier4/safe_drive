// generated from rosidl_generator_cpp/resource/idl__traits.hpp.em
// with input from sample_msg:msg/Foo.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__FOO__TRAITS_HPP_
#define SAMPLE_MSG__MSG__DETAIL__FOO__TRAITS_HPP_

#include "sample_msg/msg/detail/foo__struct.hpp"
#include <stdint.h>
#include <rosidl_runtime_cpp/traits.hpp>
#include <sstream>
#include <string>
#include <type_traits>

namespace rosidl_generator_traits
{

inline void to_yaml(
  const sample_msg::msg::Foo & msg,
  std::ostream & out, size_t indentation = 0)
{
  // member: a
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "a: ";
    value_to_yaml(msg.a, out);
    out << "\n";
  }
}  // NOLINT(readability/fn_size)

inline std::string to_yaml(const sample_msg::msg::Foo & msg)
{
  std::ostringstream out;
  to_yaml(msg, out);
  return out.str();
}

template<>
inline const char * data_type<sample_msg::msg::Foo>()
{
  return "sample_msg::msg::Foo";
}

template<>
inline const char * name<sample_msg::msg::Foo>()
{
  return "sample_msg/msg/Foo";
}

template<>
struct has_fixed_size<sample_msg::msg::Foo>
  : std::integral_constant<bool, false> {};

template<>
struct has_bounded_size<sample_msg::msg::Foo>
  : std::integral_constant<bool, false> {};

template<>
struct is_message<sample_msg::msg::Foo>
  : std::true_type {};

}  // namespace rosidl_generator_traits

#endif  // SAMPLE_MSG__MSG__DETAIL__FOO__TRAITS_HPP_
