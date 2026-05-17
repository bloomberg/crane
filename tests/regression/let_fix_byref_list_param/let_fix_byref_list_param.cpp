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
