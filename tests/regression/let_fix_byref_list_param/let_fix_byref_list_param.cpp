#include "let_fix_byref_list_param.h"

uint64_t LetFixByrefListParam::count_elements(const List<uint64_t> &xs) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    return UINT64_C(0);
  } else {
    const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
    return UINT64_C(1) + count_elements(*a1);
  }
}

uint64_t LetFixByrefListParam::sum_with_acc(const List<uint64_t> &l) {
  uint64_t _lc1_acc = UINT64_C(0);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_acc = _lc1_acc;
  const List<uint64_t> *_lc1_loop_xs = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_loop_xs->v())) {
      return _lc1_loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_lc1_loop_xs->v());
      _lc1_loop_acc = _lc1_loop_acc + a0;
      _lc1_loop_xs = crane_raw(a1);
    }
  }
}
