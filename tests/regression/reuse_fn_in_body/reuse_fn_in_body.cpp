#include "reuse_fn_in_body.h"

uint64_t ReuseFnInBody::length(const ReuseFnInBody::mylist &l) {
  {
    const ReuseFnInBody::mylist &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const ReuseFnInBody::mylist *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename ReuseFnInBody::mylist::Mycons>(
              _lc1_loop_l0->v())) {
        const auto &[a0, a1] =
            std::get<typename ReuseFnInBody::mylist::Mycons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + UINT64_C(1));
        _lc1_loop_l0 = crane_raw(a1);
      } else {
        return _lc1_loop_acc;
      }
    }
  }
}

uint64_t ReuseFnInBody::sum(const ReuseFnInBody::mylist &l) {
  {
    const ReuseFnInBody::mylist &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const ReuseFnInBody::mylist *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename ReuseFnInBody::mylist::Mycons>(
              _lc1_loop_l0->v())) {
        const auto &[a0, a1] =
            std::get<typename ReuseFnInBody::mylist::Mycons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      } else {
        return _lc1_loop_acc;
      }
    }
  }
}

/// BUG: reuse fires on the mycons branch. The body constructs
/// mycons (sum l + h) t where l is the scrutinee.
///
/// The reuse path does:
/// auto h  = std::move(_rf.d_a0);
/// auto xs = std::move(_rf.d_a1);   // _rf.d_a1 = nullptr
/// _rf.d_a0 = sum(l) + h;           // sum(l) accesses l.d_a1 = nullptr!
/// _rf.d_a1 = xs;
/// return l;
///
/// sum(l) traverses l, hitting the null d_a1 field.
/// Dereferencing null shared_ptr → CRASH.
///
/// This is similar to reuse_use_after_move but the scrutinee
/// is used through a DIFFERENT function (sum instead of length)
/// AND combined with a pattern variable in an arithmetic expression.
ReuseFnInBody::mylist ReuseFnInBody::prefix_sum(ReuseFnInBody::mylist l,
                                                bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseFnInBody::mylist::Mycons>(
            l.v_mut())) {
      auto &[a0, a1] =
          std::get<typename ReuseFnInBody::mylist::Mycons>(l.v_mut());
      return mylist::mycons((sum(l) + a0), *a1);
    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
