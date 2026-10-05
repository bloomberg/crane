#include "let_fix_tail_loop.h"

uint64_t LetFixTailLoop::sum_list(const List<uint64_t> &l) {
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

uint64_t LetFixTailLoop::length_list(const List<uint64_t> &l) {
  auto go = [](const List<uint64_t> &xs, uint64_t n) -> uint64_t {
    uint64_t _loop_n = std::move(n);
    const List<uint64_t> *_loop_xs = &xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        return _loop_n;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
        _loop_n = (UINT64_C(1) + _loop_n);
        _loop_xs = crane_raw(a1);
      }
    }
  };
  return go(l, UINT64_C(0));
}
