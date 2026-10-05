#include "let_fix_ycomb_byref.h"

uint64_t LetFixYcombByref::sum_list(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_xs = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const List<uint64_t> *_lc1_loop_xs = &_lc1_xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_xs->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_xs->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_xs = crane_raw(a1);
      }
    }
  }
}

List<uint64_t> LetFixYcombByref::zip_sum(const List<uint64_t> &xs,
                                         const List<uint64_t> &ys) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
    if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
      return List<uint64_t>::nil();
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(ys.v());
      return List<uint64_t>::cons((a0 + a00), zip_sum(*a1, *a10));
    }
  }
}

List<uint64_t> LetFixYcombByref::countdown(uint64_t k) {
  if (k <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t k_ = k - 1;
    return List<uint64_t>::cons(k, countdown(k_));
  }
}
