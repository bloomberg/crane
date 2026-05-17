#include "let_fix_tail_loop.h"

uint64_t LetFixTailLoop::sum_list(const List<uint64_t> &l) {
  auto go_impl = [](auto &_self_go, const List<uint64_t> &xs,
                    uint64_t acc) -> uint64_t {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      return _self_go(_self_go, *a1, (acc + a0));
    }
  };
  auto go = [&](const List<uint64_t> &xs, uint64_t acc) -> uint64_t {
    return go_impl(go_impl, xs, acc);
  };
  return go(l, UINT64_C(0));
}

uint64_t LetFixTailLoop::length_list(const List<uint64_t> &l) {
  return _length_list_go<uint64_t>(l, UINT64_C(0));
}
