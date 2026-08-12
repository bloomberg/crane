#include "perceus_reuse.h"

R::lst R::rev_append1(const R::lst &l, R::lst acc) {
  if (std::holds_alternative<typename R::lst::Nil>(l.v())) {
    return acc;
  } else {
    const auto &[a0, a1] = std::get<typename R::lst::Cons>(l.v());
    return rev_append1(*a1, lst::cons(a0, std::move(acc)));
  }
}

R::lst R::rev1(const R::lst &l) { return rev_append1(l, lst::nil()); }

uint64_t R::sum1(const R::lst &l) {
  if (std::holds_alternative<typename R::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename R::lst::Cons>(l.v());
    return (a0 + sum1(*a1));
  }
}
