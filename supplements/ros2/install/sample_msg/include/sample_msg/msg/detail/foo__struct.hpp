// generated from rosidl_generator_cpp/resource/idl__struct.hpp.em
// with input from sample_msg:msg/Foo.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__FOO__STRUCT_HPP_
#define SAMPLE_MSG__MSG__DETAIL__FOO__STRUCT_HPP_

#include <rosidl_runtime_cpp/bounded_vector.hpp>
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <array>
#include <memory>
#include <string>
#include <vector>


#ifndef _WIN32
# define DEPRECATED__sample_msg__msg__Foo __attribute__((deprecated))
#else
# define DEPRECATED__sample_msg__msg__Foo __declspec(deprecated)
#endif

namespace sample_msg
{

namespace msg
{

// message struct
template<class ContainerAllocator>
struct Foo_
{
  using Type = Foo_<ContainerAllocator>;

  explicit Foo_(rosidl_runtime_cpp::MessageInitialization _init = rosidl_runtime_cpp::MessageInitialization::ALL)
  {
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::ZERO == _init)
    {
      this->a = "";
    }
  }

  explicit Foo_(const ContainerAllocator & _alloc, rosidl_runtime_cpp::MessageInitialization _init = rosidl_runtime_cpp::MessageInitialization::ALL)
  : a(_alloc)
  {
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::ZERO == _init)
    {
      this->a = "";
    }
  }

  // field types and members
  using _a_type =
    std::basic_string<char, std::char_traits<char>, typename std::allocator_traits<ContainerAllocator>::template rebind_alloc<char>>;
  _a_type a;

  // setters for named parameter idiom
  Type & set__a(
    const std::basic_string<char, std::char_traits<char>, typename std::allocator_traits<ContainerAllocator>::template rebind_alloc<char>> & _arg)
  {
    this->a = _arg;
    return *this;
  }

  // constant declarations

  // pointer types
  using RawPtr =
    sample_msg::msg::Foo_<ContainerAllocator> *;
  using ConstRawPtr =
    const sample_msg::msg::Foo_<ContainerAllocator> *;
  using SharedPtr =
    std::shared_ptr<sample_msg::msg::Foo_<ContainerAllocator>>;
  using ConstSharedPtr =
    std::shared_ptr<sample_msg::msg::Foo_<ContainerAllocator> const>;

  template<typename Deleter = std::default_delete<
      sample_msg::msg::Foo_<ContainerAllocator>>>
  using UniquePtrWithDeleter =
    std::unique_ptr<sample_msg::msg::Foo_<ContainerAllocator>, Deleter>;

  using UniquePtr = UniquePtrWithDeleter<>;

  template<typename Deleter = std::default_delete<
      sample_msg::msg::Foo_<ContainerAllocator>>>
  using ConstUniquePtrWithDeleter =
    std::unique_ptr<sample_msg::msg::Foo_<ContainerAllocator> const, Deleter>;
  using ConstUniquePtr = ConstUniquePtrWithDeleter<>;

  using WeakPtr =
    std::weak_ptr<sample_msg::msg::Foo_<ContainerAllocator>>;
  using ConstWeakPtr =
    std::weak_ptr<sample_msg::msg::Foo_<ContainerAllocator> const>;

  // pointer types similar to ROS 1, use SharedPtr / ConstSharedPtr instead
  // NOTE: Can't use 'using' here because GNU C++ can't parse attributes properly
  typedef DEPRECATED__sample_msg__msg__Foo
    std::shared_ptr<sample_msg::msg::Foo_<ContainerAllocator>>
    Ptr;
  typedef DEPRECATED__sample_msg__msg__Foo
    std::shared_ptr<sample_msg::msg::Foo_<ContainerAllocator> const>
    ConstPtr;

  // comparison operators
  bool operator==(const Foo_ & other) const
  {
    if (this->a != other.a) {
      return false;
    }
    return true;
  }
  bool operator!=(const Foo_ & other) const
  {
    return !this->operator==(other);
  }
};  // struct Foo_

// alias to use template instance with default allocator
using Foo =
  sample_msg::msg::Foo_<std::allocator<void>>;

// constant definitions

}  // namespace msg

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__FOO__STRUCT_HPP_
