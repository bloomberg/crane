#include "let_fix_ycomb_byref.h"

unsigned int LetFixYcombByref::sum_list(const List<unsigned int> &l) {
  auto go_impl = [](auto &_self_go, List<unsigned int> xs,
                    unsigned int acc) -> unsigned int {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      return _self_go(_self_go, *(d_a1), (acc + d_a0));
    }
  };
  auto go = [&](List<unsigned int> xs, unsigned int acc) -> unsigned int {
    return go_impl(go_impl, xs, acc);
  };
  return go(l, 0u);
}

List<unsigned int> LetFixYcombByref::zip_sum(const List<unsigned int> &xs,
                                             const List<unsigned int> &ys) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(xs.v());
    if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(ys.v());
      return List<unsigned int>::cons((d_a0 + d_a00),
                                      zip_sum(*(d_a1), *(d_a10)));
    }
  }
}

List<unsigned int> LetFixYcombByref::countdown(const unsigned int k) {
  if (k <= 0) {
    return List<unsigned int>::nil();
  } else {
    unsigned int k_ = k - 1;
    return List<unsigned int>::cons(k, countdown(k_));
  }
}
