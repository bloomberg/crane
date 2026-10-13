#ifndef INCLUDED_LOGIC
#define INCLUDED_LOGIC

#include "obj.h"
#include <stdexcept>
#include <utility>

namespace Logic {

struct EqNotations {};

template <typename T1> T1 True_rect(T1 f) { return f; }

template <typename T1> T1 True_rec(T1 f) { return True_rect<T1>(std::move(f)); }

template <typename T1> T1 False_rect() {
  throw std::logic_error("absurd case");
}

template <typename T1>
const T1 False_rec = [](crane::obj) { return False_rect<T1>(); };

template <typename T1> T1 and_rect(const T1 &f) { return f; }

template <typename T1> T1 and_rec(const T1 &f) { return and_rect<T1>(f); }

template <typename T1, typename T2> T2 eq_rect(const T1 &, T2 f, const T1 &) {
  return f;
}

template <typename T1, typename T2>
T2 eq_rec(const T1 &_x, T2 f, const T1 &_x0) {
  return eq_rect<T1, T2>(_x, std::move(f), _x0);
}

template <typename T1, typename T2>
T2 eq_rec_r(const T1 &_x, T2 h, const T1 &_x0) {
  return eq_rect<T1, T2>(_x, std::move(h), _x0);
}

template <typename T1, typename T2>
T2 eq_rect_r(const T1 &_x, T2 h, const T1 &_x0) {
  return eq_rect<T1, T2>(_x, std::move(h), _x0);
}

template <typename T1> T1 ex_rect(const T1 &f) { return and_rect<T1>(f); }

template <typename T1> T1 ex_rec(const T1 &f) { return and_rect<T1>(f); }

template <typename T1> T1 eq_ex_rect(const T1 &f) { return and_rect<T1>(f); }

template <typename T1> T1 eq_ex_rec(const T1 &x0_) {
  return eq_ex_rect<T1>(x0_);
}

template <typename T1> T1 eq_ex_rect_ex_intro_l(const T1 &x0_) {
  return eq_ex_rect<T1>(x0_);
}

template <typename T1> T1 eq_ex_rect_ex_intro_r(const T1 &x0_) {
  return eq_ex_rect<T1>(x0_);
}

template <typename T1> T1 eq_ex_rect_ex_intro(const T1 &x0_) {
  return eq_ex_rect<T1>(x0_);
}

template <typename T1> T1 eq_ex_rect_uncurried(T1 f) {
  return eq_ex_rect<T1>([=]() { return f; }());
}

template <typename T1> T1 eq_ex_rec_uncurried(const T1 &x0_) {
  return eq_ex_rect_uncurried<T1>(x0_);
}

template <typename T1> T1 ex2_rect(const T1 &f) { return f; }

template <typename T1> T1 ex2_rec(const T1 &f) { return ex2_rect<T1>(f); }

template <typename T1> T1 eq_ex2_rect(const T1 &f) { return ex2_rect<T1>(f); }

template <typename T1> T1 eq_ex2_rec(const T1 &x0_) {
  return eq_ex2_rect<T1>(x0_);
}

template <typename T1> T1 eq_ex2_rect_ex_intro2_l(const T1 &x0_) {
  return eq_ex2_rect<T1>(x0_);
}

template <typename T1> T1 eq_ex2_rect_ex_intro2_r(const T1 &x0_) {
  return eq_ex2_rect<T1>(x0_);
}

template <typename T1> T1 eq_ex2_rect_ex_intro2(const T1 &x0_) {
  return eq_ex2_rect<T1>(x0_);
}

template <typename T1> T1 eq_ex2_rect_uncurried(T1 f) {
  return eq_ex2_rect<T1>([=]() { return f; }());
}

template <typename T1> T1 eq_ex2_rec_uncurried(const T1 &x0_) {
  return eq_ex2_rect_uncurried<T1>(x0_);
}

} // namespace Logic

#endif // INCLUDED_LOGIC
