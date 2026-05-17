#include "let_fix_tail_loop.h"

unsigned int LetFixTailLoop::sum_list(const List<unsigned int> &l) {
  auto go_impl = [](auto &_self_go, const List<unsigned int> &xs,
                    unsigned int acc) -> unsigned int {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      return _self_go(_self_go, *a1, (acc + a0));
    }
  };
  auto go = [&](const List<unsigned int> &xs,
                unsigned int acc) -> unsigned int {
    return go_impl(go_impl, xs, acc);
  };
  return go(l, 0u);
}

unsigned int LetFixTailLoop::length_list(const List<unsigned int> &l) {
  return _length_list_go<unsigned int>(l, 0u);
}
