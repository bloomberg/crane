#include <let_fix.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LetFix::local_sum(const std::shared_ptr<List<unsigned int>> &l) {
  std::function<unsigned int(unsigned int, std::shared_ptr<List<unsigned int>>)>
      go;
  go = [&](unsigned int acc,
           std::shared_ptr<List<unsigned int>> xs) -> unsigned int {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs->v())) {
      return acc;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&xs->v());
      return go((acc + _m.d_a0), _m.d_a1);
    }
  };
  return go(0u, l);
}

std::shared_ptr<List<unsigned int>> LetFix::local_flatten(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<List<unsigned int>>>::Nil>(xss->v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &_m =
        *std::get_if<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            &xss->v());
    std::function<std::shared_ptr<List<unsigned int>>(
        std::shared_ptr<List<unsigned int>>)>
        inner;
    inner = [&](std::shared_ptr<List<unsigned int>> ys)
        -> std::shared_ptr<List<unsigned int>> {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(ys->v())) {
        return local_flatten(_m.d_a1);
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&ys->v());
        return List<unsigned int>::cons(_m0.d_a0, inner(_m0.d_a1));
      }
    };
    return inner(_m.d_a0);
  }
}

__attribute__((pure)) bool
LetFix::local_mem(const unsigned int n,
                  const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return false;
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
    if (_m.d_a0 == n) {
      return true;
    } else {
      return local_mem(n, _m.d_a1);
    }
  }
}
