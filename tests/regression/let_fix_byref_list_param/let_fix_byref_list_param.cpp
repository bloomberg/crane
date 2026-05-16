#include "let_fix_byref_list_param.h"

unsigned int
LetFixByrefListParam::count_elements(const List<unsigned int> &xs) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(xs.v());
    return (1u + count_elements(*(d_a1)));
  }
}

unsigned int LetFixByrefListParam::sum_with_acc(const List<unsigned int> &l) {
  auto go_impl = [](auto &_self_go, const List<unsigned int> &xs,
                    const unsigned int acc) -> unsigned int {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      return _self_go(_self_go, *(d_a1), (acc + d_a0));
    }
  };
  auto go = [&](const List<unsigned int> &xs,
                const unsigned int acc) -> unsigned int {
    return go_impl(go_impl, xs, acc);
  };
  return go(l, 0u);
}
