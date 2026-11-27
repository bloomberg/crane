#include "let_fix.h"

uint64_t LetFix::local_sum(const List<uint64_t> &l) {
  uint64_t _lc1_acc = UINT64_C(0);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_lc1_loop_xs = &l;
  uint64_t _lc1_loop_acc = _lc1_acc;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_loop_xs->v())) {
      return _lc1_loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_lc1_loop_xs->v());
      _lc1_loop_xs = crane_raw(a1);
      _lc1_loop_acc = _lc1_loop_acc + a0;
    }
  }
}

List<uint64_t> LetFix::local_flatten(const List<List<uint64_t>> &xss) {
  if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(xss.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<List<uint64_t>>::Cons>(xss.v());
    auto inner_impl =
        [&](auto &_self_inner, const List<uint64_t> &ys) -> List<uint64_t> {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
            return local_flatten(*a1);
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(ys.v());
            return List<uint64_t>::cons(a00, _self_inner(_self_inner, *a10));
          }
        };
    return inner_impl(inner_impl, a0);
  }
}

bool LetFix::local_mem(uint64_t n, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return false;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    if (a0 == n) {
      return true;
    } else {
      return local_mem(n, *a1);
    }
  }
}
