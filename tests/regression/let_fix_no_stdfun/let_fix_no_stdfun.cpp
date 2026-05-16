#include "let_fix_no_stdfun.h"

unsigned int LetFixNoStdfun::sum_list(const List<unsigned int> &l) {
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

unsigned int LetFixNoStdfun::flat_map_sum(const List<List<unsigned int>> &xss) {
  if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(xss.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<List<unsigned int>>::Cons>(xss.v());
    auto inner_sum_impl = [](auto &_self_inner_sum,
                             const List<unsigned int> &ys,
                             const unsigned int acc) -> unsigned int {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
        return acc;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(ys.v());
        return _self_inner_sum(_self_inner_sum, *(d_a10), (acc + d_a00));
      }
    };
    auto inner_sum = [&](const List<unsigned int> &ys,
                         const unsigned int acc) -> unsigned int {
      return inner_sum_impl(inner_sum_impl, ys, acc);
    };
    return (inner_sum(d_a0, 0u) + flat_map_sum(*(d_a1)));
  }
}

List<unsigned int>
LetFixNoStdfun::flatten(const List<List<unsigned int>> &xss) {
  if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(xss.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<List<unsigned int>>::Cons>(xss.v());
    auto inner_impl = [&](auto &_self_inner,
                          const List<unsigned int> &ys) -> List<unsigned int> {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
        return flatten(*(d_a1));
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(ys.v());
        return List<unsigned int>::cons(d_a00,
                                        _self_inner(_self_inner, *(d_a10)));
      }
    };
    auto inner = [&](const List<unsigned int> &ys) -> List<unsigned int> {
      return inner_impl(inner_impl, ys);
    };
    return inner(d_a0);
  }
}
