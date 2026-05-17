#include "let_fix_nested_clone.h"

uint64_t LetFixNestedClone::sum_nested(const List<List<uint64_t>> &ll) {
  auto outer_impl = [](auto &_self_outer, const List<List<uint64_t>> &xss,
                       uint64_t acc) -> uint64_t {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(xss.v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(xss.v());
      auto inner_impl = [](auto &_self_inner, const List<uint64_t> &ys,
                           uint64_t a) -> uint64_t {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
          return a;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(ys.v());
          return _self_inner(_self_inner, *a10, (a + a00));
        }
      };
      auto inner = [&](const List<uint64_t> &ys, uint64_t a) -> uint64_t {
        return inner_impl(inner_impl, ys, a);
      };
      return _self_outer(_self_outer, *a1, (inner(a0, UINT64_C(0)) + acc));
    }
  };
  auto outer = [&](const List<List<uint64_t>> &xss, uint64_t acc) -> uint64_t {
    return outer_impl(outer_impl, xss, acc);
  };
  return outer(ll, UINT64_C(0));
}

uint64_t LetFixNestedClone::count_nested(const List<List<uint64_t>> &ll) {
  return _count_nested_outer<uint64_t>(ll, UINT64_C(0));
}
