#include <reuse_fn_in_body.h>

__attribute__((pure)) unsigned int
ReuseFnInBody::length(const ReuseFnInBody::mylist &l) {
  if (std::holds_alternative<typename ReuseFnInBody::mylist::Mycons>(l.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseFnInBody::mylist::Mycons>(l.v());
    return (1u + length(*(d_a1)));
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
ReuseFnInBody::sum(const ReuseFnInBody::mylist &l) {
  if (std::holds_alternative<typename ReuseFnInBody::mylist::Mycons>(l.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseFnInBody::mylist::Mycons>(l.v());
    return (d_a0 + sum(*(d_a1)));
  } else {
    return 0u;
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
__attribute__((pure)) ReuseFnInBody::mylist
ReuseFnInBody::prefix_sum(ReuseFnInBody::mylist l, const bool &b) {
  if (b) {
    if (std::holds_alternative<typename ReuseFnInBody::mylist::Mycons>(l.v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename ReuseFnInBody::mylist::Mycons>(l.v());
      return mylist::mycons((sum(l) + d_a0), *(d_a1));
    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
