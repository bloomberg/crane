#include "let_fix_byref_list_param.h"

uint64_t LetFixByrefListParam::count_elements(const List<uint64_t> &xs) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
    return (UINT64_C(1) + count_elements(*a1));
  }
}

uint64_t LetFixByrefListParam::sum_with_acc(const List<uint64_t> &l) {
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
