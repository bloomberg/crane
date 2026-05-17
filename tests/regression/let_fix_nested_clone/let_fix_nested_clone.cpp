#include "let_fix_nested_clone.h"

unsigned int LetFixNestedClone::sum_nested(const List<List<unsigned int>> &ll) {
  auto outer_impl = [](auto &_self_outer, const List<List<unsigned int>> &xss,
                       unsigned int acc) -> unsigned int {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            xss.v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(xss.v());
      auto inner_impl = [](auto &_self_inner, const List<unsigned int> &ys,
                           unsigned int a) -> unsigned int {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
          return a;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(ys.v());
          return _self_inner(_self_inner, *d_a10, (a + d_a00));
        }
      };
      auto inner = [&](const List<unsigned int> &ys,
                       unsigned int a) -> unsigned int {
        return inner_impl(inner_impl, ys, a);
      };
      return _self_outer(_self_outer, *d_a1, (inner(d_a0, 0u) + acc));
    }
  };
  auto outer = [&](const List<List<unsigned int>> &xss,
                   unsigned int acc) -> unsigned int {
    return outer_impl(outer_impl, xss, acc);
  };
  return outer(ll, 0u);
}

unsigned int
LetFixNestedClone::count_nested(const List<List<unsigned int>> &ll) {
  return _count_nested_outer<unsigned int>(ll, 0u);
}
