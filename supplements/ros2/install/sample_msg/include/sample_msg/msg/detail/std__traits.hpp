// generated from rosidl_generator_cpp/resource/idl__traits.hpp.em
// with input from sample_msg:msg/Std.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__STD__TRAITS_HPP_
#define SAMPLE_MSG__MSG__DETAIL__STD__TRAITS_HPP_

#include "sample_msg/msg/detail/std__struct.hpp"
#include <stdint.h>
#include <rosidl_runtime_cpp/traits.hpp>
#include <sstream>
#include <string>
#include <type_traits>

// Include directives for member types
// Member 'q'
#include "std_msgs/msg/detail/bool__traits.hpp"
// Member 'r'
#include "std_msgs/msg/detail/byte__traits.hpp"
// Member 's'
#include "std_msgs/msg/detail/byte_multi_array__traits.hpp"
// Member 't'
#include "std_msgs/msg/detail/char__traits.hpp"
// Member 'u'
#include "std_msgs/msg/detail/color_rgba__traits.hpp"
// Member 'w'
#include "std_msgs/msg/detail/empty__traits.hpp"
// Member 'x'
#include "std_msgs/msg/detail/float32__traits.hpp"
// Member 'y'
#include "std_msgs/msg/detail/float32_multi_array__traits.hpp"
// Member 'z'
#include "std_msgs/msg/detail/float64__traits.hpp"
// Member 'aa'
#include "std_msgs/msg/detail/float64_multi_array__traits.hpp"
// Member 'bb'
#include "std_msgs/msg/detail/header__traits.hpp"
// Member 'cc'
#include "std_msgs/msg/detail/int16__traits.hpp"
// Member 'dd'
#include "std_msgs/msg/detail/int16_multi_array__traits.hpp"
// Member 'ee'
#include "std_msgs/msg/detail/int32__traits.hpp"
// Member 'ff'
#include "std_msgs/msg/detail/int32_multi_array__traits.hpp"
// Member 'gg'
#include "std_msgs/msg/detail/int64__traits.hpp"
// Member 'hh'
#include "std_msgs/msg/detail/int64_multi_array__traits.hpp"
// Member 'ii'
#include "std_msgs/msg/detail/int8__traits.hpp"
// Member 'jj'
#include "std_msgs/msg/detail/int8_multi_array__traits.hpp"
// Member 'kk'
#include "std_msgs/msg/detail/multi_array_dimension__traits.hpp"
// Member 'll'
#include "std_msgs/msg/detail/multi_array_layout__traits.hpp"
// Member 'mm'
#include "std_msgs/msg/detail/string__traits.hpp"
// Member 'oo'
#include "std_msgs/msg/detail/u_int16__traits.hpp"
// Member 'pp'
#include "std_msgs/msg/detail/u_int16_multi_array__traits.hpp"
// Member 'qq'
#include "std_msgs/msg/detail/u_int32__traits.hpp"
// Member 'rr'
#include "std_msgs/msg/detail/u_int32_multi_array__traits.hpp"
// Member 'ss'
#include "std_msgs/msg/detail/u_int64__traits.hpp"
// Member 'tt'
#include "std_msgs/msg/detail/u_int64_multi_array__traits.hpp"
// Member 'uu'
#include "std_msgs/msg/detail/u_int8__traits.hpp"
// Member 'vv'
#include "std_msgs/msg/detail/u_int8_multi_array__traits.hpp"

namespace rosidl_generator_traits
{

inline void to_yaml(
  const sample_msg::msg::Std & msg,
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

  // member: b
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "b: ";
    value_to_yaml(msg.b, out);
    out << "\n";
  }

  // member: c
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "c: ";
    value_to_yaml(msg.c, out);
    out << "\n";
  }

  // member: d
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "d: ";
    value_to_yaml(msg.d, out);
    out << "\n";
  }

  // member: e
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "e: ";
    value_to_yaml(msg.e, out);
    out << "\n";
  }

  // member: f
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "f: ";
    value_to_yaml(msg.f, out);
    out << "\n";
  }

  // member: g
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "g: ";
    value_to_yaml(msg.g, out);
    out << "\n";
  }

  // member: h
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "h: ";
    value_to_yaml(msg.h, out);
    out << "\n";
  }

  // member: i
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "i: ";
    value_to_yaml(msg.i, out);
    out << "\n";
  }

  // member: j
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "j: ";
    value_to_yaml(msg.j, out);
    out << "\n";
  }

  // member: k
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "k: ";
    value_to_yaml(msg.k, out);
    out << "\n";
  }

  // member: l
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "l: ";
    value_to_yaml(msg.l, out);
    out << "\n";
  }

  // member: o
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    if (msg.o.size() == 0) {
      out << "o: []\n";
    } else {
      out << "o:\n";
      for (auto item : msg.o) {
        if (indentation > 0) {
          out << std::string(indentation, ' ');
        }
        out << "- ";
        value_to_yaml(item, out);
        out << "\n";
      }
    }
  }

  // member: p
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    if (msg.p.size() == 0) {
      out << "p: []\n";
    } else {
      out << "p:\n";
      for (auto item : msg.p) {
        if (indentation > 0) {
          out << std::string(indentation, ' ');
        }
        out << "- ";
        value_to_yaml(item, out);
        out << "\n";
      }
    }
  }

  // member: q
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "q:\n";
    to_yaml(msg.q, out, indentation + 2);
  }

  // member: r
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "r:\n";
    to_yaml(msg.r, out, indentation + 2);
  }

  // member: s
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "s:\n";
    to_yaml(msg.s, out, indentation + 2);
  }

  // member: t
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "t:\n";
    to_yaml(msg.t, out, indentation + 2);
  }

  // member: u
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "u:\n";
    to_yaml(msg.u, out, indentation + 2);
  }

  // member: w
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "w:\n";
    to_yaml(msg.w, out, indentation + 2);
  }

  // member: x
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "x:\n";
    to_yaml(msg.x, out, indentation + 2);
  }

  // member: y
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "y:\n";
    to_yaml(msg.y, out, indentation + 2);
  }

  // member: z
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "z:\n";
    to_yaml(msg.z, out, indentation + 2);
  }

  // member: aa
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "aa:\n";
    to_yaml(msg.aa, out, indentation + 2);
  }

  // member: bb
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "bb:\n";
    to_yaml(msg.bb, out, indentation + 2);
  }

  // member: cc
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "cc:\n";
    to_yaml(msg.cc, out, indentation + 2);
  }

  // member: dd
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "dd:\n";
    to_yaml(msg.dd, out, indentation + 2);
  }

  // member: ee
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "ee:\n";
    to_yaml(msg.ee, out, indentation + 2);
  }

  // member: ff
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "ff:\n";
    to_yaml(msg.ff, out, indentation + 2);
  }

  // member: gg
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "gg:\n";
    to_yaml(msg.gg, out, indentation + 2);
  }

  // member: hh
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "hh:\n";
    to_yaml(msg.hh, out, indentation + 2);
  }

  // member: ii
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "ii:\n";
    to_yaml(msg.ii, out, indentation + 2);
  }

  // member: jj
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "jj:\n";
    to_yaml(msg.jj, out, indentation + 2);
  }

  // member: kk
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "kk:\n";
    to_yaml(msg.kk, out, indentation + 2);
  }

  // member: ll
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "ll:\n";
    to_yaml(msg.ll, out, indentation + 2);
  }

  // member: mm
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "mm:\n";
    to_yaml(msg.mm, out, indentation + 2);
  }

  // member: oo
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "oo:\n";
    to_yaml(msg.oo, out, indentation + 2);
  }

  // member: pp
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "pp:\n";
    to_yaml(msg.pp, out, indentation + 2);
  }

  // member: qq
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "qq:\n";
    to_yaml(msg.qq, out, indentation + 2);
  }

  // member: rr
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "rr:\n";
    to_yaml(msg.rr, out, indentation + 2);
  }

  // member: ss
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "ss:\n";
    to_yaml(msg.ss, out, indentation + 2);
  }

  // member: tt
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "tt:\n";
    to_yaml(msg.tt, out, indentation + 2);
  }

  // member: uu
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "uu:\n";
    to_yaml(msg.uu, out, indentation + 2);
  }

  // member: vv
  {
    if (indentation > 0) {
      out << std::string(indentation, ' ');
    }
    out << "vv:\n";
    to_yaml(msg.vv, out, indentation + 2);
  }
}  // NOLINT(readability/fn_size)

inline std::string to_yaml(const sample_msg::msg::Std & msg)
{
  std::ostringstream out;
  to_yaml(msg, out);
  return out.str();
}

template<>
inline const char * data_type<sample_msg::msg::Std>()
{
  return "sample_msg::msg::Std";
}

template<>
inline const char * name<sample_msg::msg::Std>()
{
  return "sample_msg/msg/Std";
}

template<>
struct has_fixed_size<sample_msg::msg::Std>
  : std::integral_constant<bool, false> {};

template<>
struct has_bounded_size<sample_msg::msg::Std>
  : std::integral_constant<bool, false> {};

template<>
struct is_message<sample_msg::msg::Std>
  : std::true_type {};

}  // namespace rosidl_generator_traits

#endif  // SAMPLE_MSG__MSG__DETAIL__STD__TRAITS_HPP_
