#include "fix_move_capture.h"

uint64_t FixMoveCapture::length(const FixMoveCapture::mylist &l) {
  if (std::holds_alternative<typename FixMoveCapture::mylist::Mynil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename FixMoveCapture::mylist::Mycons>(l.v());
    return (UINT64_C(1) + length(*a1));
  }
}

uint64_t FixMoveCapture::sum(const FixMoveCapture::mylist &l) {
  if (std::holds_alternative<typename FixMoveCapture::mylist::Mynil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename FixMoveCapture::mylist::Mycons>(l.v());
    return (a0 + sum(*a1));
  }
}

FixMoveCapture::mylist FixMoveCapture::dup_head(FixMoveCapture::mylist l) {
  if (std::holds_alternative<typename FixMoveCapture::mylist::Mynil>(
          l.v_mut())) {
    return mylist::mynil();
  } else {
    auto &[a0, a1] =
        std::get<typename FixMoveCapture::mylist::Mycons>(l.v_mut());
    return mylist::mycons(a0, l);
  }
}

uint64_t FixMoveCapture::f(FixMoveCapture::mylist l) {
  auto go_impl = [&](auto &_self_go, uint64_t n) -> uint64_t {
    if (n <= 0) {
      return sum(l);
    } else {
      uint64_t m = n - 1;
      return (UINT64_C(1) + _self_go(_self_go, m));
    }
  };
  auto go = [&](uint64_t n) -> uint64_t { return go_impl(go_impl, n); };
  FixMoveCapture::mylist t = dup_head(l);
  return (go(UINT64_C(3)) + length(std::move(t)));
}

uint64_t FixMoveCapture::f2(FixMoveCapture::mylist l) {
  auto go_impl = [&](auto &_self_go, uint64_t n) -> uint64_t {
    if (n <= 0) {
      return sum(l);
    } else {
      uint64_t m = n - 1;
      return (UINT64_C(1) + _self_go(_self_go, m));
    }
  };
  auto go = [&](uint64_t n) -> uint64_t { return go_impl(go_impl, n); };
  uint64_t result_g = go(UINT64_C(3));
  FixMoveCapture::mylist t = dup_head(l);
  return (result_g + length(std::move(t)));
}
