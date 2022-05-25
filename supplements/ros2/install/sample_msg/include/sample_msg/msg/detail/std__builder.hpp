// generated from rosidl_generator_cpp/resource/idl__builder.hpp.em
// with input from sample_msg:msg/Std.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__STD__BUILDER_HPP_
#define SAMPLE_MSG__MSG__DETAIL__STD__BUILDER_HPP_

#include "sample_msg/msg/detail/std__struct.hpp"
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <utility>


namespace sample_msg
{

namespace msg
{

namespace builder
{

class Init_Std_vv
{
public:
  explicit Init_Std_vv(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  ::sample_msg::msg::Std vv(::sample_msg::msg::Std::_vv_type arg)
  {
    msg_.vv = std::move(arg);
    return std::move(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_uu
{
public:
  explicit Init_Std_uu(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_vv uu(::sample_msg::msg::Std::_uu_type arg)
  {
    msg_.uu = std::move(arg);
    return Init_Std_vv(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_tt
{
public:
  explicit Init_Std_tt(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_uu tt(::sample_msg::msg::Std::_tt_type arg)
  {
    msg_.tt = std::move(arg);
    return Init_Std_uu(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_ss
{
public:
  explicit Init_Std_ss(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_tt ss(::sample_msg::msg::Std::_ss_type arg)
  {
    msg_.ss = std::move(arg);
    return Init_Std_tt(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_rr
{
public:
  explicit Init_Std_rr(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_ss rr(::sample_msg::msg::Std::_rr_type arg)
  {
    msg_.rr = std::move(arg);
    return Init_Std_ss(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_qq
{
public:
  explicit Init_Std_qq(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_rr qq(::sample_msg::msg::Std::_qq_type arg)
  {
    msg_.qq = std::move(arg);
    return Init_Std_rr(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_pp
{
public:
  explicit Init_Std_pp(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_qq pp(::sample_msg::msg::Std::_pp_type arg)
  {
    msg_.pp = std::move(arg);
    return Init_Std_qq(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_oo
{
public:
  explicit Init_Std_oo(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_pp oo(::sample_msg::msg::Std::_oo_type arg)
  {
    msg_.oo = std::move(arg);
    return Init_Std_pp(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_mm
{
public:
  explicit Init_Std_mm(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_oo mm(::sample_msg::msg::Std::_mm_type arg)
  {
    msg_.mm = std::move(arg);
    return Init_Std_oo(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_ll
{
public:
  explicit Init_Std_ll(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_mm ll(::sample_msg::msg::Std::_ll_type arg)
  {
    msg_.ll = std::move(arg);
    return Init_Std_mm(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_kk
{
public:
  explicit Init_Std_kk(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_ll kk(::sample_msg::msg::Std::_kk_type arg)
  {
    msg_.kk = std::move(arg);
    return Init_Std_ll(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_jj
{
public:
  explicit Init_Std_jj(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_kk jj(::sample_msg::msg::Std::_jj_type arg)
  {
    msg_.jj = std::move(arg);
    return Init_Std_kk(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_ii
{
public:
  explicit Init_Std_ii(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_jj ii(::sample_msg::msg::Std::_ii_type arg)
  {
    msg_.ii = std::move(arg);
    return Init_Std_jj(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_hh
{
public:
  explicit Init_Std_hh(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_ii hh(::sample_msg::msg::Std::_hh_type arg)
  {
    msg_.hh = std::move(arg);
    return Init_Std_ii(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_gg
{
public:
  explicit Init_Std_gg(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_hh gg(::sample_msg::msg::Std::_gg_type arg)
  {
    msg_.gg = std::move(arg);
    return Init_Std_hh(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_ff
{
public:
  explicit Init_Std_ff(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_gg ff(::sample_msg::msg::Std::_ff_type arg)
  {
    msg_.ff = std::move(arg);
    return Init_Std_gg(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_ee
{
public:
  explicit Init_Std_ee(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_ff ee(::sample_msg::msg::Std::_ee_type arg)
  {
    msg_.ee = std::move(arg);
    return Init_Std_ff(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_dd
{
public:
  explicit Init_Std_dd(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_ee dd(::sample_msg::msg::Std::_dd_type arg)
  {
    msg_.dd = std::move(arg);
    return Init_Std_ee(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_cc
{
public:
  explicit Init_Std_cc(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_dd cc(::sample_msg::msg::Std::_cc_type arg)
  {
    msg_.cc = std::move(arg);
    return Init_Std_dd(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_bb
{
public:
  explicit Init_Std_bb(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_cc bb(::sample_msg::msg::Std::_bb_type arg)
  {
    msg_.bb = std::move(arg);
    return Init_Std_cc(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_aa
{
public:
  explicit Init_Std_aa(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_bb aa(::sample_msg::msg::Std::_aa_type arg)
  {
    msg_.aa = std::move(arg);
    return Init_Std_bb(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_z
{
public:
  explicit Init_Std_z(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_aa z(::sample_msg::msg::Std::_z_type arg)
  {
    msg_.z = std::move(arg);
    return Init_Std_aa(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_y
{
public:
  explicit Init_Std_y(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_z y(::sample_msg::msg::Std::_y_type arg)
  {
    msg_.y = std::move(arg);
    return Init_Std_z(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_x
{
public:
  explicit Init_Std_x(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_y x(::sample_msg::msg::Std::_x_type arg)
  {
    msg_.x = std::move(arg);
    return Init_Std_y(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_w
{
public:
  explicit Init_Std_w(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_x w(::sample_msg::msg::Std::_w_type arg)
  {
    msg_.w = std::move(arg);
    return Init_Std_x(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_u
{
public:
  explicit Init_Std_u(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_w u(::sample_msg::msg::Std::_u_type arg)
  {
    msg_.u = std::move(arg);
    return Init_Std_w(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_t
{
public:
  explicit Init_Std_t(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_u t(::sample_msg::msg::Std::_t_type arg)
  {
    msg_.t = std::move(arg);
    return Init_Std_u(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_s
{
public:
  explicit Init_Std_s(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_t s(::sample_msg::msg::Std::_s_type arg)
  {
    msg_.s = std::move(arg);
    return Init_Std_t(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_r
{
public:
  explicit Init_Std_r(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_s r(::sample_msg::msg::Std::_r_type arg)
  {
    msg_.r = std::move(arg);
    return Init_Std_s(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_q
{
public:
  explicit Init_Std_q(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_r q(::sample_msg::msg::Std::_q_type arg)
  {
    msg_.q = std::move(arg);
    return Init_Std_r(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_p
{
public:
  explicit Init_Std_p(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_q p(::sample_msg::msg::Std::_p_type arg)
  {
    msg_.p = std::move(arg);
    return Init_Std_q(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_o
{
public:
  explicit Init_Std_o(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_p o(::sample_msg::msg::Std::_o_type arg)
  {
    msg_.o = std::move(arg);
    return Init_Std_p(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_l
{
public:
  explicit Init_Std_l(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_o l(::sample_msg::msg::Std::_l_type arg)
  {
    msg_.l = std::move(arg);
    return Init_Std_o(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_k
{
public:
  explicit Init_Std_k(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_l k(::sample_msg::msg::Std::_k_type arg)
  {
    msg_.k = std::move(arg);
    return Init_Std_l(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_j
{
public:
  explicit Init_Std_j(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_k j(::sample_msg::msg::Std::_j_type arg)
  {
    msg_.j = std::move(arg);
    return Init_Std_k(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_i
{
public:
  explicit Init_Std_i(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_j i(::sample_msg::msg::Std::_i_type arg)
  {
    msg_.i = std::move(arg);
    return Init_Std_j(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_h
{
public:
  explicit Init_Std_h(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_i h(::sample_msg::msg::Std::_h_type arg)
  {
    msg_.h = std::move(arg);
    return Init_Std_i(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_g
{
public:
  explicit Init_Std_g(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_h g(::sample_msg::msg::Std::_g_type arg)
  {
    msg_.g = std::move(arg);
    return Init_Std_h(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_f
{
public:
  explicit Init_Std_f(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_g f(::sample_msg::msg::Std::_f_type arg)
  {
    msg_.f = std::move(arg);
    return Init_Std_g(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_e
{
public:
  explicit Init_Std_e(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_f e(::sample_msg::msg::Std::_e_type arg)
  {
    msg_.e = std::move(arg);
    return Init_Std_f(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_d
{
public:
  explicit Init_Std_d(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_e d(::sample_msg::msg::Std::_d_type arg)
  {
    msg_.d = std::move(arg);
    return Init_Std_e(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_c
{
public:
  explicit Init_Std_c(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_d c(::sample_msg::msg::Std::_c_type arg)
  {
    msg_.c = std::move(arg);
    return Init_Std_d(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_b
{
public:
  explicit Init_Std_b(::sample_msg::msg::Std & msg)
  : msg_(msg)
  {}
  Init_Std_c b(::sample_msg::msg::Std::_b_type arg)
  {
    msg_.b = std::move(arg);
    return Init_Std_c(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

class Init_Std_a
{
public:
  Init_Std_a()
  : msg_(::rosidl_runtime_cpp::MessageInitialization::SKIP)
  {}
  Init_Std_b a(::sample_msg::msg::Std::_a_type arg)
  {
    msg_.a = std::move(arg);
    return Init_Std_b(msg_);
  }

private:
  ::sample_msg::msg::Std msg_;
};

}  // namespace builder

}  // namespace msg

template<typename MessageType>
auto build();

template<>
inline
auto build<::sample_msg::msg::Std>()
{
  return sample_msg::msg::builder::Init_Std_a();
}

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__STD__BUILDER_HPP_
