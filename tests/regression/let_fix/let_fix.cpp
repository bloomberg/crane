#include <let_fix.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LetFix::local_sum(const List<unsigned int> &l) {
  std::function<unsigned int(unsigned int, List<unsigned int>)> go;
  go = [&](unsigned int acc, List<unsigned int> xs) -> unsigned int {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      return go((acc + d_a0), *(d_a1));
    }
  };
  return go(0u, l);
}

__attribute__((pure)) List<unsigned int>
LetFix::local_flatten(const List<List<unsigned int>> &xss) {
  if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(xss.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<List<unsigned int>>::Cons>(xss.v());
    List<List<unsigned int>> d_a1_value = *(d_a1);
    std::function<List<unsigned int>(List<unsigned int>)> inner;
    inner = [&](List<unsigned int> ys) -> List<unsigned int> {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
        return local_flatten(d_a1_value);
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(ys.v());
        return List<unsigned int>::cons(d_a00, inner(*(d_a10)));
      }
    };
    return inner(clone_as_value<List<unsigned int>>(d_a0));
  }
}

__attribute__((pure)) bool LetFix::local_mem(const unsigned int &n,
                                             const List<unsigned int> &l) {
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
