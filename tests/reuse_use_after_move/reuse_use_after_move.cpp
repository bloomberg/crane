#include "reuse_use_after_move.h"

uint64_t ReuseUseAfterMove::length(const ReuseUseAfterMove::mylist &l) {
  if (std::holds_alternative<typename ReuseUseAfterMove::mylist::Mycons>(
          l.v())) {
    const auto &[a0, a1] =
        std::get<typename ReuseUseAfterMove::mylist::Mycons>(l.v());
    return (UINT64_C(1) + length(*a1));
  } else {
    return UINT64_C(0);
  }
}

uint64_t ReuseUseAfterMove::sum(const ReuseUseAfterMove::mylist &l) {
  if (std::holds_alternative<typename ReuseUseAfterMove::mylist::Mycons>(
          l.v())) {
    const auto &[a0, a1] =
        std::get<typename ReuseUseAfterMove::mylist::Mycons>(l.v());
    return (a0 + sum(*a1));
  } else {
    return UINT64_C(0);
  }
}

ReuseUseAfterMove::mylist
ReuseUseAfterMove::rewrite_head(ReuseUseAfterMove::mylist l, bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseUseAfterMove::mylist::Mycons>(
            l.v_mut())) {
      auto &[a0, a1] =
          std::get<typename ReuseUseAfterMove::mylist::Mycons>(l.v_mut());
      return mylist::mycons(length(l), *a1);
    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}

ReuseUseAfterMove::mylist
ReuseUseAfterMove::rewrite_head_sum(ReuseUseAfterMove::mylist l, bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseUseAfterMove::mylist::Mycons>(
            l.v_mut())) {
      auto &[a0, a1] =
          std::get<typename ReuseUseAfterMove::mylist::Mycons>(l.v_mut());
      return mylist::mycons(sum(l), *a1);
    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
