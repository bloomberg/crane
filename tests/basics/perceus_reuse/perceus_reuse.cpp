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
  {
    const R::lst &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const R::lst *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename R::lst::Nil>(_lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename R::lst::Cons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}
