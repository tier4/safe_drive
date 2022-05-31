// generated from rosidl_generator_cpp/resource/idl__struct.hpp.em
// with input from sample_msg:msg/Buz.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__BUZ__STRUCT_HPP_
#define SAMPLE_MSG__MSG__DETAIL__BUZ__STRUCT_HPP_

#include <rosidl_runtime_cpp/bounded_vector.hpp>
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <array>
#include <memory>
#include <string>
#include <vector>


#ifndef _WIN32
# define DEPRECATED__sample_msg__msg__Buz __attribute__((deprecated))
#else
# define DEPRECATED__sample_msg__msg__Buz __declspec(deprecated)
#endif

namespace sample_msg
{

namespace msg
{

// message struct
template<class ContainerAllocator>
struct Buz_
{
  using Type = Buz_<ContainerAllocator>;

  explicit Buz_(rosidl_runtime_cpp::MessageInitialization _init = rosidl_runtime_cpp::MessageInitialization::ALL)
  {
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::ZERO == _init)
    {
      this->c = "";
    }
  }

  explicit Buz_(const ContainerAllocator & _alloc, rosidl_runtime_cpp::MessageInitialization _init = rosidl_runtime_cpp::MessageInitialization::ALL)
  : c(_alloc)
  {
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::ZERO == _init)
    {
      this->c = "";
    }
  }

  // field types and members
  using _c_type =
    std::basic_string<char, std::char_traits<char>, typename std::allocator_traits<ContainerAllocator>::template rebind_alloc<char>>;
  _c_type c;

  // setters for named parameter idiom
  Type & set__c(
    const std::basic_string<char, std::char_traits<char>, typename std::allocator_traits<ContainerAllocator>::template rebind_alloc<char>> & _arg)
  {
    this->c = _arg;
    return *this;
  }

  // constant declarations

  // pointer types
  using RawPtr =
    sample_msg::msg::Buz_<ContainerAllocator> *;
  using ConstRawPtr =
    const sample_msg::msg::Buz_<ContainerAllocator> *;
  using SharedPtr =
    std::shared_ptr<sample_msg::msg::Buz_<ContainerAllocator>>;
  using ConstSharedPtr =
    std::shared_ptr<sample_msg::msg::Buz_<ContainerAllocator> const>;

  template<typename Deleter = std::default_delete<
      sample_msg::msg::Buz_<ContainerAllocator>>>
  using UniquePtrWithDeleter =
    std::unique_ptr<sample_msg::msg::Buz_<ContainerAllocator>, Deleter>;

  using UniquePtr = UniquePtrWithDeleter<>;

  template<typename Deleter = std::default_delete<
      sample_msg::msg::Buz_<ContainerAllocator>>>
  using ConstUniquePtrWithDeleter =
    std::unique_ptr<sample_msg::msg::Buz_<ContainerAllocator> const, Deleter>;
  using ConstUniquePtr = ConstUniquePtrWithDeleter<>;

  using WeakPtr =
    std::weak_ptr<sample_msg::msg::Buz_<ContainerAllocator>>;
  using ConstWeakPtr =
    std::weak_ptr<sample_msg::msg::Buz_<ContainerAllocator> const>;

  // pointer types similar to ROS 1, use SharedPtr / ConstSharedPtr instead
  // NOTE: Can't use 'using' here because GNU C++ can't parse attributes properly
  typedef DEPRECATED__sample_msg__msg__Buz
    std::shared_ptr<sample_msg::msg::Buz_<ContainerAllocator>>
    Ptr;
  typedef DEPRECATED__sample_msg__msg__Buz
    std::shared_ptr<sample_msg::msg::Buz_<ContainerAllocator> const>
    ConstPtr;

  // comparison operators
  bool operator==(const Buz_ & other) const
  {
    if (this->c != other.c) {
      return false;
    }
    return true;
  }
  bool operator!=(const Buz_ & other) const
  {
    return !this->operator==(other);
  }
};  // struct Buz_

// alias to use template instance with default allocator
using Buz =
  sample_msg::msg::Buz_<std::allocator<void>>;

// constant definitions

}  // namespace msg

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__BUZ__STRUCT_HPP_
