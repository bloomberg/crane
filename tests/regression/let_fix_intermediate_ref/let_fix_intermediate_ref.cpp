#include "let_fix_intermediate_ref.h"

unsigned int
LetFixIntermediateRef::sum_heads(const List<List<unsigned int>> &ll) {
  auto go_impl = [](auto &_self_go, const List<List<unsigned int>> &xss,
                    unsigned int acc) -> unsigned int {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            xss.v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<unsigned int>>::Cons>(xss.v());
      unsigned int hd = [&]() {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(a0.v())) {
          return 0u;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<unsigned int>::Cons>(a0.v());
          return a00;
        }
      }();
      return _self_go(_self_go, *a1, (acc + hd));
    }
  };
  auto go = [&](const List<List<unsigned int>> &xss,
                unsigned int acc) -> unsigned int {
    return go_impl(go_impl, xss, acc);
  };
  return go(ll, 0u);
}

unsigned int LetFixIntermediateRef::zip_sum(const List<unsigned int> &l1,
                                            const List<unsigned int> &l2) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l1.v());
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
      return 0u;
    } else {
      const auto &[a00, a10] =
          std::get<typename List<unsigned int>::Cons>(l2.v());
      return ((a0 + a00) + zip_sum(*a1, *a10));
    }
  }
}
