// generated from rosidl_generator_cpp/resource/idl__struct.hpp.em
// with input from sample_msg:msg/Num.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__NUM__STRUCT_HPP_
#define SAMPLE_MSG__MSG__DETAIL__NUM__STRUCT_HPP_

#include <rosidl_runtime_cpp/bounded_vector.hpp>
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <array>
#include <memory>
#include <string>
#include <vector>


#ifndef _WIN32
# define DEPRECATED__sample_msg__msg__Num __attribute__((deprecated))
#else
# define DEPRECATED__sample_msg__msg__Num __declspec(deprecated)
#endif

namespace sample_msg
{

namespace msg
{

// message struct
template<class ContainerAllocator>
struct Num_
{
  using Type = Num_<ContainerAllocator>;

  explicit Num_(rosidl_runtime_cpp::MessageInitialization _init = rosidl_runtime_cpp::MessageInitialization::ALL)
  {
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::ZERO == _init)
    {
      this->num = 0ll;
    }
  }

  explicit Num_(const ContainerAllocator & _alloc, rosidl_runtime_cpp::MessageInitialization _init = rosidl_runtime_cpp::MessageInitialization::ALL)
  {
    (void)_alloc;
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::ZERO == _init)
    {
      this->num = 0ll;
    }
  }

  // field types and members
  using _num_type =
    int64_t;
  _num_type num;

  // setters for named parameter idiom
  Type & set__num(
    const int64_t & _arg)
  {
    this->num = _arg;
    return *this;
  }

  // constant declarations

  // pointer types
  using RawPtr =
    sample_msg::msg::Num_<ContainerAllocator> *;
  using ConstRawPtr =
    const sample_msg::msg::Num_<ContainerAllocator> *;
  using SharedPtr =
    std::shared_ptr<sample_msg::msg::Num_<ContainerAllocator>>;
  using ConstSharedPtr =
    std::shared_ptr<sample_msg::msg::Num_<ContainerAllocator> const>;

  template<typename Deleter = std::default_delete<
      sample_msg::msg::Num_<ContainerAllocator>>>
  using UniquePtrWithDeleter =
    std::unique_ptr<sample_msg::msg::Num_<ContainerAllocator>, Deleter>;

  using UniquePtr = UniquePtrWithDeleter<>;

  template<typename Deleter = std::default_delete<
      sample_msg::msg::Num_<ContainerAllocator>>>
  using ConstUniquePtrWithDeleter =
    std::unique_ptr<sample_msg::msg::Num_<ContainerAllocator> const, Deleter>;
  using ConstUniquePtr = ConstUniquePtrWithDeleter<>;

  using WeakPtr =
    std::weak_ptr<sample_msg::msg::Num_<ContainerAllocator>>;
  using ConstWeakPtr =
    std::weak_ptr<sample_msg::msg::Num_<ContainerAllocator> const>;

  // pointer types similar to ROS 1, use SharedPtr / ConstSharedPtr instead
  // NOTE: Can't use 'using' here because GNU C++ can't parse attributes properly
  typedef DEPRECATED__sample_msg__msg__Num
    std::shared_ptr<sample_msg::msg::Num_<ContainerAllocator>>
    Ptr;
  typedef DEPRECATED__sample_msg__msg__Num
    std::shared_ptr<sample_msg::msg::Num_<ContainerAllocator> const>
    ConstPtr;

  // comparison operators
  bool operator==(const Num_ & other) const
  {
    if (this->num != other.num) {
      return false;
    }
    return true;
  }
  bool operator!=(const Num_ & other) const
  {
    return !this->operator==(other);
  }
};  // struct Num_

// alias to use template instance with default allocator
using Num =
  sample_msg::msg::Num_<std::allocator<void>>;

// constant definitions

}  // namespace msg

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__NUM__STRUCT_HPP_
