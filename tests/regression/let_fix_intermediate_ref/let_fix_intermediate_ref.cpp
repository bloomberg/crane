#include "let_fix_intermediate_ref.h"

unsigned int
LetFixIntermediateRef::sum_heads(const List<List<unsigned int>> &ll) {
  auto go_impl = [](auto &_self_go, const List<List<unsigned int>> &xss,
                    const unsigned int acc) -> unsigned int {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            xss.v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(xss.v());
      unsigned int hd = [&]() {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                d_a0.v())) {
          return 0u;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(d_a0.v());
          return d_a00;
        }
      }();
      return _self_go(_self_go, *(d_a1), (acc + hd));
    }
  };
  auto go = [&](const List<List<unsigned int>> &xss,
                const unsigned int acc) -> unsigned int {
    return go_impl(go_impl, xss, acc);
  };
  return go(ll, 0u);
}

unsigned int LetFixIntermediateRef::zip_sum(const List<unsigned int> &l1,
                                            const List<unsigned int> &l2) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l1.v());
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(l2.v());
      return ((d_a0 + d_a00) + zip_sum(*(d_a1), *(d_a10)));
    }
  }
}
