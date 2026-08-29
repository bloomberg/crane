#include "reuse_fn_in_body.h"

uint64_t ReuseFnInBody::length(const ReuseFnInBody::mylist &l) {
  if (std::holds_alternative<typename ReuseFnInBody::mylist::Mycons>(l.v())) {
    const auto &[a0, a1] =
        std::get<typename ReuseFnInBody::mylist::Mycons>(l.v());
    return (UINT64_C(1) + length(*a1));
  } else {
    return UINT64_C(0);
  }
}

uint64_t ReuseFnInBody::sum(const ReuseFnInBody::mylist &l) {
  if (std::holds_alternative<typename ReuseFnInBody::mylist::Mycons>(l.v())) {
    const auto &[a0, a1] =
        std::get<typename ReuseFnInBody::mylist::Mycons>(l.v());
    return (a0 + sum(*a1));
  } else {
    return UINT64_C(0);
  }
}

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
