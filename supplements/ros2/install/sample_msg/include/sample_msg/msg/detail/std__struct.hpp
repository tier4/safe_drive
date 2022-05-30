// generated from rosidl_generator_cpp/resource/idl__struct.hpp.em
// with input from sample_msg:msg/Std.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__STD__STRUCT_HPP_
#define SAMPLE_MSG__MSG__DETAIL__STD__STRUCT_HPP_

#include <rosidl_runtime_cpp/bounded_vector.hpp>
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <array>
#include <memory>
#include <string>
#include <vector>


// Include directives for member types
// Member 'q'
#include "std_msgs/msg/detail/bool__struct.hpp"
// Member 'r'
#include "std_msgs/msg/detail/byte__struct.hpp"
// Member 's'
#include "std_msgs/msg/detail/byte_multi_array__struct.hpp"
// Member 't'
#include "std_msgs/msg/detail/char__struct.hpp"
// Member 'u'
#include "std_msgs/msg/detail/color_rgba__struct.hpp"
// Member 'w'
#include "std_msgs/msg/detail/empty__struct.hpp"
// Member 'x'
#include "std_msgs/msg/detail/float32__struct.hpp"
// Member 'y'
#include "std_msgs/msg/detail/float32_multi_array__struct.hpp"
// Member 'z'
#include "std_msgs/msg/detail/float64__struct.hpp"
// Member 'aa'
#include "std_msgs/msg/detail/float64_multi_array__struct.hpp"
// Member 'bb'
#include "std_msgs/msg/detail/header__struct.hpp"
// Member 'cc'
#include "std_msgs/msg/detail/int16__struct.hpp"
// Member 'dd'
#include "std_msgs/msg/detail/int16_multi_array__struct.hpp"
// Member 'ee'
#include "std_msgs/msg/detail/int32__struct.hpp"
// Member 'ff'
#include "std_msgs/msg/detail/int32_multi_array__struct.hpp"
// Member 'gg'
#include "std_msgs/msg/detail/int64__struct.hpp"
// Member 'hh'
#include "std_msgs/msg/detail/int64_multi_array__struct.hpp"
// Member 'ii'
#include "std_msgs/msg/detail/int8__struct.hpp"
// Member 'jj'
#include "std_msgs/msg/detail/int8_multi_array__struct.hpp"
// Member 'kk'
#include "std_msgs/msg/detail/multi_array_dimension__struct.hpp"
// Member 'll'
#include "std_msgs/msg/detail/multi_array_layout__struct.hpp"
// Member 'mm'
#include "std_msgs/msg/detail/string__struct.hpp"
// Member 'oo'
#include "std_msgs/msg/detail/u_int16__struct.hpp"
// Member 'pp'
#include "std_msgs/msg/detail/u_int16_multi_array__struct.hpp"
// Member 'qq'
#include "std_msgs/msg/detail/u_int32__struct.hpp"
// Member 'rr'
#include "std_msgs/msg/detail/u_int32_multi_array__struct.hpp"
// Member 'ss'
#include "std_msgs/msg/detail/u_int64__struct.hpp"
// Member 'tt'
#include "std_msgs/msg/detail/u_int64_multi_array__struct.hpp"
// Member 'uu'
#include "std_msgs/msg/detail/u_int8__struct.hpp"
// Member 'vv'
#include "std_msgs/msg/detail/u_int8_multi_array__struct.hpp"

#ifndef _WIN32
# define DEPRECATED__sample_msg__msg__Std __attribute__((deprecated))
#else
# define DEPRECATED__sample_msg__msg__Std __declspec(deprecated)
#endif

namespace sample_msg
{

namespace msg
{

// message struct
template<class ContainerAllocator>
struct Std_
{
  using Type = Std_<ContainerAllocator>;

  explicit Std_(rosidl_runtime_cpp::MessageInitialization _init = rosidl_runtime_cpp::MessageInitialization::ALL)
  : q(_init),
    r(_init),
    s(_init),
    t(_init),
    u(_init),
    w(_init),
    x(_init),
    y(_init),
    z(_init),
    aa(_init),
    bb(_init),
    cc(_init),
    dd(_init),
    ee(_init),
    ff(_init),
    gg(_init),
    hh(_init),
    ii(_init),
    jj(_init),
    kk(_init),
    ll(_init),
    mm(_init),
    oo(_init),
    pp(_init),
    qq(_init),
    rr(_init),
    ss(_init),
    tt(_init),
    uu(_init),
    vv(_init)
  {
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::DEFAULTS_ONLY == _init)
    {
      this->ww = 40l;
    } else if (rosidl_runtime_cpp::MessageInitialization::ZERO == _init) {
      this->a = false;
      this->b = 0;
      this->c = 0;
      this->d = 0;
      this->e = 0;
      this->f = 0l;
      this->g = 0ul;
      this->h = 0ll;
      this->i = 0ull;
      this->j = 0.0f;
      this->k = 0.0;
      this->l = "";
      std::fill<typename std::array<int32_t, 10>::iterator, int32_t>(this->p.begin(), this->p.end(), 0l);
      this->ww = 0l;
    }
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::ZERO == _init)
    {
      this->a = false;
      this->b = 0;
      this->c = 0;
      this->d = 0;
      this->e = 0;
      this->f = 0l;
      this->g = 0ul;
      this->h = 0ll;
      this->i = 0ull;
      this->j = 0.0f;
      this->k = 0.0;
      this->l = "";
      std::fill<typename std::array<int32_t, 10>::iterator, int32_t>(this->p.begin(), this->p.end(), 0l);
    }
  }

  explicit Std_(const ContainerAllocator & _alloc, rosidl_runtime_cpp::MessageInitialization _init = rosidl_runtime_cpp::MessageInitialization::ALL)
  : l(_alloc),
    p(_alloc),
    q(_alloc, _init),
    r(_alloc, _init),
    s(_alloc, _init),
    t(_alloc, _init),
    u(_alloc, _init),
    w(_alloc, _init),
    x(_alloc, _init),
    y(_alloc, _init),
    z(_alloc, _init),
    aa(_alloc, _init),
    bb(_alloc, _init),
    cc(_alloc, _init),
    dd(_alloc, _init),
    ee(_alloc, _init),
    ff(_alloc, _init),
    gg(_alloc, _init),
    hh(_alloc, _init),
    ii(_alloc, _init),
    jj(_alloc, _init),
    kk(_alloc, _init),
    ll(_alloc, _init),
    mm(_alloc, _init),
    oo(_alloc, _init),
    pp(_alloc, _init),
    qq(_alloc, _init),
    rr(_alloc, _init),
    ss(_alloc, _init),
    tt(_alloc, _init),
    uu(_alloc, _init),
    vv(_alloc, _init)
  {
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::DEFAULTS_ONLY == _init)
    {
      this->ww = 40l;
    } else if (rosidl_runtime_cpp::MessageInitialization::ZERO == _init) {
      this->a = false;
      this->b = 0;
      this->c = 0;
      this->d = 0;
      this->e = 0;
      this->f = 0l;
      this->g = 0ul;
      this->h = 0ll;
      this->i = 0ull;
      this->j = 0.0f;
      this->k = 0.0;
      this->l = "";
      std::fill<typename std::array<int32_t, 10>::iterator, int32_t>(this->p.begin(), this->p.end(), 0l);
      this->ww = 0l;
    }
    if (rosidl_runtime_cpp::MessageInitialization::ALL == _init ||
      rosidl_runtime_cpp::MessageInitialization::ZERO == _init)
    {
      this->a = false;
      this->b = 0;
      this->c = 0;
      this->d = 0;
      this->e = 0;
      this->f = 0l;
      this->g = 0ul;
      this->h = 0ll;
      this->i = 0ull;
      this->j = 0.0f;
      this->k = 0.0;
      this->l = "";
      std::fill<typename std::array<int32_t, 10>::iterator, int32_t>(this->p.begin(), this->p.end(), 0l);
    }
  }

  // field types and members
  using _a_type =
    bool;
  _a_type a;
  using _b_type =
    int8_t;
  _b_type b;
  using _c_type =
    uint8_t;
  _c_type c;
  using _d_type =
    int16_t;
  _d_type d;
  using _e_type =
    uint16_t;
  _e_type e;
  using _f_type =
    int32_t;
  _f_type f;
  using _g_type =
    uint32_t;
  _g_type g;
  using _h_type =
    int64_t;
  _h_type h;
  using _i_type =
    uint64_t;
  _i_type i;
  using _j_type =
    float;
  _j_type j;
  using _k_type =
    double;
  _k_type k;
  using _l_type =
    std::basic_string<char, std::char_traits<char>, typename std::allocator_traits<ContainerAllocator>::template rebind_alloc<char>>;
  _l_type l;
  using _o_type =
    std::vector<int32_t, typename std::allocator_traits<ContainerAllocator>::template rebind_alloc<int32_t>>;
  _o_type o;
  using _p_type =
    std::array<int32_t, 10>;
  _p_type p;
  using _q_type =
    std_msgs::msg::Bool_<ContainerAllocator>;
  _q_type q;
  using _r_type =
    std_msgs::msg::Byte_<ContainerAllocator>;
  _r_type r;
  using _s_type =
    std_msgs::msg::ByteMultiArray_<ContainerAllocator>;
  _s_type s;
  using _t_type =
    std_msgs::msg::Char_<ContainerAllocator>;
  _t_type t;
  using _u_type =
    std_msgs::msg::ColorRGBA_<ContainerAllocator>;
  _u_type u;
  using _w_type =
    std_msgs::msg::Empty_<ContainerAllocator>;
  _w_type w;
  using _x_type =
    std_msgs::msg::Float32_<ContainerAllocator>;
  _x_type x;
  using _y_type =
    std_msgs::msg::Float32MultiArray_<ContainerAllocator>;
  _y_type y;
  using _z_type =
    std_msgs::msg::Float64_<ContainerAllocator>;
  _z_type z;
  using _aa_type =
    std_msgs::msg::Float64MultiArray_<ContainerAllocator>;
  _aa_type aa;
  using _bb_type =
    std_msgs::msg::Header_<ContainerAllocator>;
  _bb_type bb;
  using _cc_type =
    std_msgs::msg::Int16_<ContainerAllocator>;
  _cc_type cc;
  using _dd_type =
    std_msgs::msg::Int16MultiArray_<ContainerAllocator>;
  _dd_type dd;
  using _ee_type =
    std_msgs::msg::Int32_<ContainerAllocator>;
  _ee_type ee;
  using _ff_type =
    std_msgs::msg::Int32MultiArray_<ContainerAllocator>;
  _ff_type ff;
  using _gg_type =
    std_msgs::msg::Int64_<ContainerAllocator>;
  _gg_type gg;
  using _hh_type =
    std_msgs::msg::Int64MultiArray_<ContainerAllocator>;
  _hh_type hh;
  using _ii_type =
    std_msgs::msg::Int8_<ContainerAllocator>;
  _ii_type ii;
  using _jj_type =
    std_msgs::msg::Int8MultiArray_<ContainerAllocator>;
  _jj_type jj;
  using _kk_type =
    std_msgs::msg::MultiArrayDimension_<ContainerAllocator>;
  _kk_type kk;
  using _ll_type =
    std_msgs::msg::MultiArrayLayout_<ContainerAllocator>;
  _ll_type ll;
  using _mm_type =
    std_msgs::msg::String_<ContainerAllocator>;
  _mm_type mm;
  using _oo_type =
    std_msgs::msg::UInt16_<ContainerAllocator>;
  _oo_type oo;
  using _pp_type =
    std_msgs::msg::UInt16MultiArray_<ContainerAllocator>;
  _pp_type pp;
  using _qq_type =
    std_msgs::msg::UInt32_<ContainerAllocator>;
  _qq_type qq;
  using _rr_type =
    std_msgs::msg::UInt32MultiArray_<ContainerAllocator>;
  _rr_type rr;
  using _ss_type =
    std_msgs::msg::UInt64_<ContainerAllocator>;
  _ss_type ss;
  using _tt_type =
    std_msgs::msg::UInt64MultiArray_<ContainerAllocator>;
  _tt_type tt;
  using _uu_type =
    std_msgs::msg::UInt8_<ContainerAllocator>;
  _uu_type uu;
  using _vv_type =
    std_msgs::msg::UInt8MultiArray_<ContainerAllocator>;
  _vv_type vv;
  using _ww_type =
    int32_t;
  _ww_type ww;

  // setters for named parameter idiom
  Type & set__a(
    const bool & _arg)
  {
    this->a = _arg;
    return *this;
  }
  Type & set__b(
    const int8_t & _arg)
  {
    this->b = _arg;
    return *this;
  }
  Type & set__c(
    const uint8_t & _arg)
  {
    this->c = _arg;
    return *this;
  }
  Type & set__d(
    const int16_t & _arg)
  {
    this->d = _arg;
    return *this;
  }
  Type & set__e(
    const uint16_t & _arg)
  {
    this->e = _arg;
    return *this;
  }
  Type & set__f(
    const int32_t & _arg)
  {
    this->f = _arg;
    return *this;
  }
  Type & set__g(
    const uint32_t & _arg)
  {
    this->g = _arg;
    return *this;
  }
  Type & set__h(
    const int64_t & _arg)
  {
    this->h = _arg;
    return *this;
  }
  Type & set__i(
    const uint64_t & _arg)
  {
    this->i = _arg;
    return *this;
  }
  Type & set__j(
    const float & _arg)
  {
    this->j = _arg;
    return *this;
  }
  Type & set__k(
    const double & _arg)
  {
    this->k = _arg;
    return *this;
  }
  Type & set__l(
    const std::basic_string<char, std::char_traits<char>, typename std::allocator_traits<ContainerAllocator>::template rebind_alloc<char>> & _arg)
  {
    this->l = _arg;
    return *this;
  }
  Type & set__o(
    const std::vector<int32_t, typename std::allocator_traits<ContainerAllocator>::template rebind_alloc<int32_t>> & _arg)
  {
    this->o = _arg;
    return *this;
  }
  Type & set__p(
    const std::array<int32_t, 10> & _arg)
  {
    this->p = _arg;
    return *this;
  }
  Type & set__q(
    const std_msgs::msg::Bool_<ContainerAllocator> & _arg)
  {
    this->q = _arg;
    return *this;
  }
  Type & set__r(
    const std_msgs::msg::Byte_<ContainerAllocator> & _arg)
  {
    this->r = _arg;
    return *this;
  }
  Type & set__s(
    const std_msgs::msg::ByteMultiArray_<ContainerAllocator> & _arg)
  {
    this->s = _arg;
    return *this;
  }
  Type & set__t(
    const std_msgs::msg::Char_<ContainerAllocator> & _arg)
  {
    this->t = _arg;
    return *this;
  }
  Type & set__u(
    const std_msgs::msg::ColorRGBA_<ContainerAllocator> & _arg)
  {
    this->u = _arg;
    return *this;
  }
  Type & set__w(
    const std_msgs::msg::Empty_<ContainerAllocator> & _arg)
  {
    this->w = _arg;
    return *this;
  }
  Type & set__x(
    const std_msgs::msg::Float32_<ContainerAllocator> & _arg)
  {
    this->x = _arg;
    return *this;
  }
  Type & set__y(
    const std_msgs::msg::Float32MultiArray_<ContainerAllocator> & _arg)
  {
    this->y = _arg;
    return *this;
  }
  Type & set__z(
    const std_msgs::msg::Float64_<ContainerAllocator> & _arg)
  {
    this->z = _arg;
    return *this;
  }
  Type & set__aa(
    const std_msgs::msg::Float64MultiArray_<ContainerAllocator> & _arg)
  {
    this->aa = _arg;
    return *this;
  }
  Type & set__bb(
    const std_msgs::msg::Header_<ContainerAllocator> & _arg)
  {
    this->bb = _arg;
    return *this;
  }
  Type & set__cc(
    const std_msgs::msg::Int16_<ContainerAllocator> & _arg)
  {
    this->cc = _arg;
    return *this;
  }
  Type & set__dd(
    const std_msgs::msg::Int16MultiArray_<ContainerAllocator> & _arg)
  {
    this->dd = _arg;
    return *this;
  }
  Type & set__ee(
    const std_msgs::msg::Int32_<ContainerAllocator> & _arg)
  {
    this->ee = _arg;
    return *this;
  }
  Type & set__ff(
    const std_msgs::msg::Int32MultiArray_<ContainerAllocator> & _arg)
  {
    this->ff = _arg;
    return *this;
  }
  Type & set__gg(
    const std_msgs::msg::Int64_<ContainerAllocator> & _arg)
  {
    this->gg = _arg;
    return *this;
  }
  Type & set__hh(
    const std_msgs::msg::Int64MultiArray_<ContainerAllocator> & _arg)
  {
    this->hh = _arg;
    return *this;
  }
  Type & set__ii(
    const std_msgs::msg::Int8_<ContainerAllocator> & _arg)
  {
    this->ii = _arg;
    return *this;
  }
  Type & set__jj(
    const std_msgs::msg::Int8MultiArray_<ContainerAllocator> & _arg)
  {
    this->jj = _arg;
    return *this;
  }
  Type & set__kk(
    const std_msgs::msg::MultiArrayDimension_<ContainerAllocator> & _arg)
  {
    this->kk = _arg;
    return *this;
  }
  Type & set__ll(
    const std_msgs::msg::MultiArrayLayout_<ContainerAllocator> & _arg)
  {
    this->ll = _arg;
    return *this;
  }
  Type & set__mm(
    const std_msgs::msg::String_<ContainerAllocator> & _arg)
  {
    this->mm = _arg;
    return *this;
  }
  Type & set__oo(
    const std_msgs::msg::UInt16_<ContainerAllocator> & _arg)
  {
    this->oo = _arg;
    return *this;
  }
  Type & set__pp(
    const std_msgs::msg::UInt16MultiArray_<ContainerAllocator> & _arg)
  {
    this->pp = _arg;
    return *this;
  }
  Type & set__qq(
    const std_msgs::msg::UInt32_<ContainerAllocator> & _arg)
  {
    this->qq = _arg;
    return *this;
  }
  Type & set__rr(
    const std_msgs::msg::UInt32MultiArray_<ContainerAllocator> & _arg)
  {
    this->rr = _arg;
    return *this;
  }
  Type & set__ss(
    const std_msgs::msg::UInt64_<ContainerAllocator> & _arg)
  {
    this->ss = _arg;
    return *this;
  }
  Type & set__tt(
    const std_msgs::msg::UInt64MultiArray_<ContainerAllocator> & _arg)
  {
    this->tt = _arg;
    return *this;
  }
  Type & set__uu(
    const std_msgs::msg::UInt8_<ContainerAllocator> & _arg)
  {
    this->uu = _arg;
    return *this;
  }
  Type & set__vv(
    const std_msgs::msg::UInt8MultiArray_<ContainerAllocator> & _arg)
  {
    this->vv = _arg;
    return *this;
  }
  Type & set__ww(
    const int32_t & _arg)
  {
    this->ww = _arg;
    return *this;
  }

  // constant declarations
  static constexpr int32_t XX =
    20;

  // pointer types
  using RawPtr =
    sample_msg::msg::Std_<ContainerAllocator> *;
  using ConstRawPtr =
    const sample_msg::msg::Std_<ContainerAllocator> *;
  using SharedPtr =
    std::shared_ptr<sample_msg::msg::Std_<ContainerAllocator>>;
  using ConstSharedPtr =
    std::shared_ptr<sample_msg::msg::Std_<ContainerAllocator> const>;

  template<typename Deleter = std::default_delete<
      sample_msg::msg::Std_<ContainerAllocator>>>
  using UniquePtrWithDeleter =
    std::unique_ptr<sample_msg::msg::Std_<ContainerAllocator>, Deleter>;

  using UniquePtr = UniquePtrWithDeleter<>;

  template<typename Deleter = std::default_delete<
      sample_msg::msg::Std_<ContainerAllocator>>>
  using ConstUniquePtrWithDeleter =
    std::unique_ptr<sample_msg::msg::Std_<ContainerAllocator> const, Deleter>;
  using ConstUniquePtr = ConstUniquePtrWithDeleter<>;

  using WeakPtr =
    std::weak_ptr<sample_msg::msg::Std_<ContainerAllocator>>;
  using ConstWeakPtr =
    std::weak_ptr<sample_msg::msg::Std_<ContainerAllocator> const>;

  // pointer types similar to ROS 1, use SharedPtr / ConstSharedPtr instead
  // NOTE: Can't use 'using' here because GNU C++ can't parse attributes properly
  typedef DEPRECATED__sample_msg__msg__Std
    std::shared_ptr<sample_msg::msg::Std_<ContainerAllocator>>
    Ptr;
  typedef DEPRECATED__sample_msg__msg__Std
    std::shared_ptr<sample_msg::msg::Std_<ContainerAllocator> const>
    ConstPtr;

  // comparison operators
  bool operator==(const Std_ & other) const
  {
    if (this->a != other.a) {
      return false;
    }
    if (this->b != other.b) {
      return false;
    }
    if (this->c != other.c) {
      return false;
    }
    if (this->d != other.d) {
      return false;
    }
    if (this->e != other.e) {
      return false;
    }
    if (this->f != other.f) {
      return false;
    }
    if (this->g != other.g) {
      return false;
    }
    if (this->h != other.h) {
      return false;
    }
    if (this->i != other.i) {
      return false;
    }
    if (this->j != other.j) {
      return false;
    }
    if (this->k != other.k) {
      return false;
    }
    if (this->l != other.l) {
      return false;
    }
    if (this->o != other.o) {
      return false;
    }
    if (this->p != other.p) {
      return false;
    }
    if (this->q != other.q) {
      return false;
    }
    if (this->r != other.r) {
      return false;
    }
    if (this->s != other.s) {
      return false;
    }
    if (this->t != other.t) {
      return false;
    }
    if (this->u != other.u) {
      return false;
    }
    if (this->w != other.w) {
      return false;
    }
    if (this->x != other.x) {
      return false;
    }
    if (this->y != other.y) {
      return false;
    }
    if (this->z != other.z) {
      return false;
    }
    if (this->aa != other.aa) {
      return false;
    }
    if (this->bb != other.bb) {
      return false;
    }
    if (this->cc != other.cc) {
      return false;
    }
    if (this->dd != other.dd) {
      return false;
    }
    if (this->ee != other.ee) {
      return false;
    }
    if (this->ff != other.ff) {
      return false;
    }
    if (this->gg != other.gg) {
      return false;
    }
    if (this->hh != other.hh) {
      return false;
    }
    if (this->ii != other.ii) {
      return false;
    }
    if (this->jj != other.jj) {
      return false;
    }
    if (this->kk != other.kk) {
      return false;
    }
    if (this->ll != other.ll) {
      return false;
    }
    if (this->mm != other.mm) {
      return false;
    }
    if (this->oo != other.oo) {
      return false;
    }
    if (this->pp != other.pp) {
      return false;
    }
    if (this->qq != other.qq) {
      return false;
    }
    if (this->rr != other.rr) {
      return false;
    }
    if (this->ss != other.ss) {
      return false;
    }
    if (this->tt != other.tt) {
      return false;
    }
    if (this->uu != other.uu) {
      return false;
    }
    if (this->vv != other.vv) {
      return false;
    }
    if (this->ww != other.ww) {
      return false;
    }
    return true;
  }
  bool operator!=(const Std_ & other) const
  {
    return !this->operator==(other);
  }
};  // struct Std_

// alias to use template instance with default allocator
using Std =
  sample_msg::msg::Std_<std::allocator<void>>;

// constant definitions
template<typename ContainerAllocator>
constexpr int32_t Std_<ContainerAllocator>::XX;

}  // namespace msg

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__STD__STRUCT_HPP_
