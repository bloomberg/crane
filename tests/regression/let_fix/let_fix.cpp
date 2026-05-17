#include "let_fix.h"

unsigned int LetFix::local_sum(const List<unsigned int> &l) {
  auto go_impl = [](auto &_self_go, unsigned int acc,
                    const List<unsigned int> &xs) -> unsigned int {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      return _self_go(_self_go, (acc + a0), *a1);
    }
  };
  auto go = [&](unsigned int acc,
                const List<unsigned int> &xs) -> unsigned int {
    return go_impl(go_impl, acc, xs);
  };
  return go(0u, l);
}

List<unsigned int> LetFix::local_flatten(const List<List<unsigned int>> &xss) {
  if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(xss.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<List<unsigned int>>::Cons>(xss.v());
    auto inner_impl = [&](auto &_self_inner,
                          const List<unsigned int> &ys) -> List<unsigned int> {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
        return local_flatten(*a1);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<unsigned int>::Cons>(ys.v());
        return List<unsigned int>::cons(a00, _self_inner(_self_inner, *a10));
      }
    };
    auto inner = [&](const List<unsigned int> &ys) -> List<unsigned int> {
      return inner_impl(inner_impl, ys);
    };
    return inner(a0);
  }
}

bool LetFix::local_mem(unsigned int n, const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return false;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    if (a0 == n) {
      return true;
    } else {
      return local_mem(n, *a1);
    }
  }
}
