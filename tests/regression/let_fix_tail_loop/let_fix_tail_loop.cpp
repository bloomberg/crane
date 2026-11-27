#include "let_fix_tail_loop.h"

uint64_t LetFixTailLoop::sum_list(const List<uint64_t> &l) {
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
      _lc1_loop_acc = (_lc1_loop_acc + a0);
      _lc1_loop_xs = crane_raw(a1);
    }
  }
}

uint64_t LetFixTailLoop::length_list(const List<uint64_t> &l) {
  uint64_t _lc1_n = UINT64_C(0);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_n = _lc1_n;
  const List<uint64_t> *_lc1_loop_xs = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_loop_xs->v())) {
      return _lc1_loop_n;
    } else {
      const auto &[_, a1] =
          std::get<typename List<uint64_t>::Cons>(_lc1_loop_xs->v());
      _lc1_loop_n = (UINT64_C(1) + _lc1_loop_n);
      _lc1_loop_xs = crane_raw(a1);
    }
  }
}
