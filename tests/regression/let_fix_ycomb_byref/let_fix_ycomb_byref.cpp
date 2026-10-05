#include "let_fix_ycomb_byref.h"

uint64_t LetFixYcombByref::sum_list(const List<uint64_t> &l) {
  auto go = [](const List<uint64_t> &xs, uint64_t acc) -> uint64_t {
    uint64_t _loop_acc = std::move(acc);
    const List<uint64_t> *_loop_xs = &xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
        _loop_acc = (_loop_acc + a0);
        _loop_xs = crane_raw(a1);
      }
    }
  };
  return go(l, UINT64_C(0));
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
