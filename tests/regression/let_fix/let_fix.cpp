#include "let_fix.h"

unsigned int LetFix::local_sum(const List<unsigned int> &l) {
  auto go_impl = [](auto &_self_go, unsigned int acc,
                    List<unsigned int> xs) -> unsigned int {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      return _self_go(_self_go, (acc + d_a0), *(d_a1));
    }
  };
  auto go = [&](unsigned int acc, List<unsigned int> xs) -> unsigned int {
    return go_impl(go_impl, acc, xs);
  };
  return go(0u, l);
}

List<unsigned int> LetFix::local_flatten(const List<List<unsigned int>> &xss) {
  if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(xss.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<List<unsigned int>>::Cons>(xss.v());
    auto inner_impl = [&](auto &_self_inner,
                          List<unsigned int> ys) -> List<unsigned int> {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
        return local_flatten(*(d_a1));
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(ys.v());
        return List<unsigned int>::cons(d_a00,
                                        _self_inner(_self_inner, *(d_a10)));
      }
    };
    auto inner = [&](List<unsigned int> ys) -> List<unsigned int> {
      return inner_impl(inner_impl, ys);
    };
    return inner(d_a0);
  }
}

bool LetFix::local_mem(const unsigned int n, const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return false;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    if (d_a0 == n) {
      return true;
    } else {
      return local_mem(n, *(d_a1));
    }
  }
}
