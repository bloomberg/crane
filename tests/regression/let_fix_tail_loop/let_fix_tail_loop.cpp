#include "let_fix_tail_loop.h"

uint64_t LetFixTailLoop::sum_list(const List<uint64_t> &l) {
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

uint64_t LetFixTailLoop::length_list(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_xs = l;
    uint64_t _lc1_n = UINT64_C(0);
    uint64_t _lc1_loop_n = std::move(_lc1_n);
    const List<uint64_t> *_lc1_loop_xs = &_lc1_xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_xs->v())) {
        return _lc1_loop_n;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_xs->v());
        _lc1_loop_n = (UINT64_C(1) + _lc1_loop_n);
        _lc1_loop_xs = crane_raw(a1);
      }
    }
  }
}
