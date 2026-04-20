#include <reuse_use_after_move.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ReuseUseAfterMove::length(const std::shared_ptr<ReuseUseAfterMove::mylist> &l) {
  if (std::holds_alternative<typename ReuseUseAfterMove::mylist::Mycons>(
          l->v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseUseAfterMove::mylist::Mycons>(l->v());
    return (1u + length(d_a1));
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
ReuseUseAfterMove::sum(const std::shared_ptr<ReuseUseAfterMove::mylist> &l) {
  if (std::holds_alternative<typename ReuseUseAfterMove::mylist::Mycons>(
          l->v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseUseAfterMove::mylist::Mycons>(l->v());
    return (d_a0 + sum(d_a1));
  } else {
    return 0u;
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
std::shared_ptr<ReuseUseAfterMove::mylist>
ReuseUseAfterMove::rewrite_head(std::shared_ptr<ReuseUseAfterMove::mylist> l,
                                const bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseUseAfterMove::mylist::Mycons>(
            l->v())) {
      if (l.use_count() == 1) {
        auto &_rf =
            std::get<typename ReuseUseAfterMove::mylist::Mycons>(l->v_mut());
        std::shared_ptr<ReuseUseAfterMove::mylist> xs = std::move(_rf.d_a1);
        _rf.d_a0 = length(l);
        _rf.d_a1 = xs;
        return l;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename ReuseUseAfterMove::mylist::Mycons>(l->v());
        return mylist::mycons(length(l), d_a1);
      }

    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}

/// test2: Use sum instead of length — same bug pattern.
std::shared_ptr<ReuseUseAfterMove::mylist> ReuseUseAfterMove::rewrite_head_sum(
    std::shared_ptr<ReuseUseAfterMove::mylist> l, const bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseUseAfterMove::mylist::Mycons>(
            l->v())) {
      if (l.use_count() == 1) {
        auto &_rf =
            std::get<typename ReuseUseAfterMove::mylist::Mycons>(l->v_mut());
        std::shared_ptr<ReuseUseAfterMove::mylist> xs = std::move(_rf.d_a1);
        _rf.d_a0 = sum(l);
        _rf.d_a1 = xs;
        return l;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename ReuseUseAfterMove::mylist::Mycons>(l->v());
        return mylist::mycons(sum(l), d_a1);
      }

    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
