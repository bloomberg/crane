#include "fix_move_capture.h"

unsigned int FixMoveCapture::length(const FixMoveCapture::mylist &l) {
  if (std::holds_alternative<typename FixMoveCapture::mylist::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename FixMoveCapture::mylist::Mycons>(l.v());
    return (1u + length(*a1));
  }
}

unsigned int FixMoveCapture::sum(const FixMoveCapture::mylist &l) {
  if (std::holds_alternative<typename FixMoveCapture::mylist::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename FixMoveCapture::mylist::Mycons>(l.v());
    return (a0 + sum(*a1));
  }
}

/// dup_head stores l in the constructor → l escapes → owned.
/// This means the caller passes l by value (move semantics).
FixMoveCapture::mylist FixMoveCapture::dup_head(FixMoveCapture::mylist l) {
  if (std::holds_alternative<typename FixMoveCapture::mylist::Mynil>(
          l.v_mut())) {
    return mylist::mynil();
  } else {
    auto &[a0, a1] =
        std::get<typename FixMoveCapture::mylist::Mycons>(l.v_mut());
    return mylist::mycons(std::move(a0), l);
  }
}

/// f l: defines a local fixpoint go that captures l by &.
/// Then let t := dup_head l in ...:
/// - dup_head takes l by value (owned, because l escapes in its body)
/// - Crane sees that l (dead_in_a) is not free in continuation g 3 + length t
/// - Generates dup_head(std::move(l))
/// - l is now null in caller scope
/// - g(3) calls fixpoint, which accesses l via & → null → CRASH
unsigned int FixMoveCapture::f(FixMoveCapture::mylist l) {
  auto go_impl = [&](auto &_self_go, unsigned int n) -> unsigned int {
    if (n <= 0) {
      return sum(l);
    } else {
      unsigned int m = n - 1;
      return (1u + _self_go(_self_go, m));
    }
  };
  auto go = [&](unsigned int n) -> unsigned int { return go_impl(go_impl, n); };
  FixMoveCapture::mylist t = dup_head(l);
  return (go(3u) + length(std::move(t)));
}

/// Even simpler: use the fixpoint, then pass l to a consuming
/// function. The addition's evaluation order is unspecified in C++,
/// so we use a let-binding to force the order.
unsigned int FixMoveCapture::f2(FixMoveCapture::mylist l) {
  auto go_impl = [&](auto &_self_go, unsigned int n) -> unsigned int {
    if (n <= 0) {
      return sum(l);
    } else {
      unsigned int m = n - 1;
      return (1u + _self_go(_self_go, m));
    }
  };
  auto go = [&](unsigned int n) -> unsigned int { return go_impl(go_impl, n); };
  unsigned int result_g = go(3u);
  FixMoveCapture::mylist t = dup_head(l);
  return (result_g + length(std::move(t)));
}
