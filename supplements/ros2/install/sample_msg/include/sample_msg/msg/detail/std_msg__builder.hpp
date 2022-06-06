// generated from rosidl_generator_cpp/resource/idl__builder.hpp.em
// with input from sample_msg:msg/StdMsg.idl
// generated code does not contain a copyright notice

#ifndef SAMPLE_MSG__MSG__DETAIL__STD_MSG__BUILDER_HPP_
#define SAMPLE_MSG__MSG__DETAIL__STD_MSG__BUILDER_HPP_

#include "sample_msg/msg/detail/std_msg__struct.hpp"
#include <rosidl_runtime_cpp/message_initialization.hpp>
#include <algorithm>
#include <utility>


namespace sample_msg
{

namespace msg
{

namespace builder
{

class Init_StdMsg_ww
{
public:
  explicit Init_StdMsg_ww(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  ::sample_msg::msg::StdMsg ww(::sample_msg::msg::StdMsg::_ww_type arg)
  {
    msg_.ww = std::move(arg);
    return std::move(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_vv
{
public:
  explicit Init_StdMsg_vv(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_ww vv(::sample_msg::msg::StdMsg::_vv_type arg)
  {
    msg_.vv = std::move(arg);
    return Init_StdMsg_ww(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_uu
{
public:
  explicit Init_StdMsg_uu(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_vv uu(::sample_msg::msg::StdMsg::_uu_type arg)
  {
    msg_.uu = std::move(arg);
    return Init_StdMsg_vv(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_tt
{
public:
  explicit Init_StdMsg_tt(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_uu tt(::sample_msg::msg::StdMsg::_tt_type arg)
  {
    msg_.tt = std::move(arg);
    return Init_StdMsg_uu(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_ss
{
public:
  explicit Init_StdMsg_ss(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_tt ss(::sample_msg::msg::StdMsg::_ss_type arg)
  {
    msg_.ss = std::move(arg);
    return Init_StdMsg_tt(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_rr
{
public:
  explicit Init_StdMsg_rr(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_ss rr(::sample_msg::msg::StdMsg::_rr_type arg)
  {
    msg_.rr = std::move(arg);
    return Init_StdMsg_ss(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_qq
{
public:
  explicit Init_StdMsg_qq(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_rr qq(::sample_msg::msg::StdMsg::_qq_type arg)
  {
    msg_.qq = std::move(arg);
    return Init_StdMsg_rr(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_pp
{
public:
  explicit Init_StdMsg_pp(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_qq pp(::sample_msg::msg::StdMsg::_pp_type arg)
  {
    msg_.pp = std::move(arg);
    return Init_StdMsg_qq(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_oo
{
public:
  explicit Init_StdMsg_oo(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_pp oo(::sample_msg::msg::StdMsg::_oo_type arg)
  {
    msg_.oo = std::move(arg);
    return Init_StdMsg_pp(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_mm
{
public:
  explicit Init_StdMsg_mm(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_oo mm(::sample_msg::msg::StdMsg::_mm_type arg)
  {
    msg_.mm = std::move(arg);
    return Init_StdMsg_oo(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_ll
{
public:
  explicit Init_StdMsg_ll(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_mm ll(::sample_msg::msg::StdMsg::_ll_type arg)
  {
    msg_.ll = std::move(arg);
    return Init_StdMsg_mm(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_kk
{
public:
  explicit Init_StdMsg_kk(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_ll kk(::sample_msg::msg::StdMsg::_kk_type arg)
  {
    msg_.kk = std::move(arg);
    return Init_StdMsg_ll(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_jj
{
public:
  explicit Init_StdMsg_jj(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_kk jj(::sample_msg::msg::StdMsg::_jj_type arg)
  {
    msg_.jj = std::move(arg);
    return Init_StdMsg_kk(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_ii
{
public:
  explicit Init_StdMsg_ii(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_jj ii(::sample_msg::msg::StdMsg::_ii_type arg)
  {
    msg_.ii = std::move(arg);
    return Init_StdMsg_jj(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_hh
{
public:
  explicit Init_StdMsg_hh(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_ii hh(::sample_msg::msg::StdMsg::_hh_type arg)
  {
    msg_.hh = std::move(arg);
    return Init_StdMsg_ii(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_gg
{
public:
  explicit Init_StdMsg_gg(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_hh gg(::sample_msg::msg::StdMsg::_gg_type arg)
  {
    msg_.gg = std::move(arg);
    return Init_StdMsg_hh(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_ff
{
public:
  explicit Init_StdMsg_ff(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_gg ff(::sample_msg::msg::StdMsg::_ff_type arg)
  {
    msg_.ff = std::move(arg);
    return Init_StdMsg_gg(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_ee
{
public:
  explicit Init_StdMsg_ee(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_ff ee(::sample_msg::msg::StdMsg::_ee_type arg)
  {
    msg_.ee = std::move(arg);
    return Init_StdMsg_ff(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_dd
{
public:
  explicit Init_StdMsg_dd(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_ee dd(::sample_msg::msg::StdMsg::_dd_type arg)
  {
    msg_.dd = std::move(arg);
    return Init_StdMsg_ee(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_cc
{
public:
  explicit Init_StdMsg_cc(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_dd cc(::sample_msg::msg::StdMsg::_cc_type arg)
  {
    msg_.cc = std::move(arg);
    return Init_StdMsg_dd(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_bb
{
public:
  explicit Init_StdMsg_bb(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_cc bb(::sample_msg::msg::StdMsg::_bb_type arg)
  {
    msg_.bb = std::move(arg);
    return Init_StdMsg_cc(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_aa
{
public:
  explicit Init_StdMsg_aa(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_bb aa(::sample_msg::msg::StdMsg::_aa_type arg)
  {
    msg_.aa = std::move(arg);
    return Init_StdMsg_bb(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_z
{
public:
  explicit Init_StdMsg_z(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_aa z(::sample_msg::msg::StdMsg::_z_type arg)
  {
    msg_.z = std::move(arg);
    return Init_StdMsg_aa(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_y
{
public:
  explicit Init_StdMsg_y(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_z y(::sample_msg::msg::StdMsg::_y_type arg)
  {
    msg_.y = std::move(arg);
    return Init_StdMsg_z(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_x
{
public:
  explicit Init_StdMsg_x(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_y x(::sample_msg::msg::StdMsg::_x_type arg)
  {
    msg_.x = std::move(arg);
    return Init_StdMsg_y(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_w
{
public:
  explicit Init_StdMsg_w(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_x w(::sample_msg::msg::StdMsg::_w_type arg)
  {
    msg_.w = std::move(arg);
    return Init_StdMsg_x(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_u
{
public:
  explicit Init_StdMsg_u(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_w u(::sample_msg::msg::StdMsg::_u_type arg)
  {
    msg_.u = std::move(arg);
    return Init_StdMsg_w(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_t
{
public:
  explicit Init_StdMsg_t(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_u t(::sample_msg::msg::StdMsg::_t_type arg)
  {
    msg_.t = std::move(arg);
    return Init_StdMsg_u(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_s
{
public:
  explicit Init_StdMsg_s(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_t s(::sample_msg::msg::StdMsg::_s_type arg)
  {
    msg_.s = std::move(arg);
    return Init_StdMsg_t(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_r
{
public:
  explicit Init_StdMsg_r(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_s r(::sample_msg::msg::StdMsg::_r_type arg)
  {
    msg_.r = std::move(arg);
    return Init_StdMsg_s(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_q
{
public:
  explicit Init_StdMsg_q(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_r q(::sample_msg::msg::StdMsg::_q_type arg)
  {
    msg_.q = std::move(arg);
    return Init_StdMsg_r(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_limited
{
public:
  explicit Init_StdMsg_limited(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_q limited(::sample_msg::msg::StdMsg::_limited_type arg)
  {
    msg_.limited = std::move(arg);
    return Init_StdMsg_q(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_p
{
public:
  explicit Init_StdMsg_p(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_limited p(::sample_msg::msg::StdMsg::_p_type arg)
  {
    msg_.p = std::move(arg);
    return Init_StdMsg_limited(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_o
{
public:
  explicit Init_StdMsg_o(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_p o(::sample_msg::msg::StdMsg::_o_type arg)
  {
    msg_.o = std::move(arg);
    return Init_StdMsg_p(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_l
{
public:
  explicit Init_StdMsg_l(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_o l(::sample_msg::msg::StdMsg::_l_type arg)
  {
    msg_.l = std::move(arg);
    return Init_StdMsg_o(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_k
{
public:
  explicit Init_StdMsg_k(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_l k(::sample_msg::msg::StdMsg::_k_type arg)
  {
    msg_.k = std::move(arg);
    return Init_StdMsg_l(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_j
{
public:
  explicit Init_StdMsg_j(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_k j(::sample_msg::msg::StdMsg::_j_type arg)
  {
    msg_.j = std::move(arg);
    return Init_StdMsg_k(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_i
{
public:
  explicit Init_StdMsg_i(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_j i(::sample_msg::msg::StdMsg::_i_type arg)
  {
    msg_.i = std::move(arg);
    return Init_StdMsg_j(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_h
{
public:
  explicit Init_StdMsg_h(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_i h(::sample_msg::msg::StdMsg::_h_type arg)
  {
    msg_.h = std::move(arg);
    return Init_StdMsg_i(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_g
{
public:
  explicit Init_StdMsg_g(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_h g(::sample_msg::msg::StdMsg::_g_type arg)
  {
    msg_.g = std::move(arg);
    return Init_StdMsg_h(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_f
{
public:
  explicit Init_StdMsg_f(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_g f(::sample_msg::msg::StdMsg::_f_type arg)
  {
    msg_.f = std::move(arg);
    return Init_StdMsg_g(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_e
{
public:
  explicit Init_StdMsg_e(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_f e(::sample_msg::msg::StdMsg::_e_type arg)
  {
    msg_.e = std::move(arg);
    return Init_StdMsg_f(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_d
{
public:
  explicit Init_StdMsg_d(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_e d(::sample_msg::msg::StdMsg::_d_type arg)
  {
    msg_.d = std::move(arg);
    return Init_StdMsg_e(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_c
{
public:
  explicit Init_StdMsg_c(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_d c(::sample_msg::msg::StdMsg::_c_type arg)
  {
    msg_.c = std::move(arg);
    return Init_StdMsg_d(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_b
{
public:
  explicit Init_StdMsg_b(::sample_msg::msg::StdMsg & msg)
  : msg_(msg)
  {}
  Init_StdMsg_c b(::sample_msg::msg::StdMsg::_b_type arg)
  {
    msg_.b = std::move(arg);
    return Init_StdMsg_c(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

class Init_StdMsg_a
{
public:
  Init_StdMsg_a()
  : msg_(::rosidl_runtime_cpp::MessageInitialization::SKIP)
  {}
  Init_StdMsg_b a(::sample_msg::msg::StdMsg::_a_type arg)
  {
    msg_.a = std::move(arg);
    return Init_StdMsg_b(msg_);
  }

private:
  ::sample_msg::msg::StdMsg msg_;
};

}  // namespace builder

}  // namespace msg

template<typename MessageType>
auto build();

template<>
inline
auto build<::sample_msg::msg::StdMsg>()
{
  return sample_msg::msg::builder::Init_StdMsg_a();
}

}  // namespace sample_msg

#endif  // SAMPLE_MSG__MSG__DETAIL__STD_MSG__BUILDER_HPP_
