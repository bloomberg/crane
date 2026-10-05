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

/// BUG: The reuse optimization fires because:
/// 1. l escapes in the else branch (returned in tail position)
/// -> infer_owned_params marks l as owned (pass by value)
/// 2. The mycons branch has tail constructor mycons with arity 2 = 2
/// -> find_reuse_candidates finds it as a candidate
/// 3. mycons is at index 0 -> List.hd picks it
/// 4. At runtime, use_count() == 1 holds for fresh values
///
/// The reuse branch does:
/// auto x  = std::move(_rf.d_a0);   // unsigned int, trivial
/// auto xs = std::move(_rf.d_a1);   // shared_ptr -> NULL
/// _rf.d_a0 = length(l);            // length accesses l.d_a1 which is NULL!
/// _rf.d_a1 = xs;                   // restore xs
/// return l;
///
/// length(l) traverses l, hitting the null d_a1 field.
/// Dereferencing null shared_ptr -> CRASH.
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

/// test2: Use sum instead of length — same bug pattern.
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
