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
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) -> unsigned int {
              return acc;
            },
            [&](const typename List<unsigned int>::Cons &_args)
                -> unsigned int { return go((acc + _args.d_a0), _args.d_a1); }},
        xs->v());
  };
  return go(0u, l);
}

std::shared_ptr<List<unsigned int>> LetFix::local_flatten(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<List<unsigned int>>>::Nil &)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::nil();
          },
          [](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                 &_args) -> std::shared_ptr<List<unsigned int>> {
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<List<unsigned int>>)>
                inner;
            inner = [&](std::shared_ptr<List<unsigned int>> ys)
                -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &)
                          -> std::shared_ptr<List<unsigned int>> {
                        return local_flatten(_args.d_a1);
                      },
                      [&](const typename List<unsigned int>::Cons &_args0)
                          -> std::shared_ptr<List<unsigned int>> {
                        return List<unsigned int>::cons(_args0.d_a0,
                                                        inner(_args0.d_a1));
                      }},
                  ys->v());
            };
            return inner(_args.d_a0);
          }},
      xss->v());
}

__attribute__((pure)) bool
LetFix::local_mem(const unsigned int n,
                  const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil &) -> bool {
                   return false;
                 },
                 [&](const typename List<unsigned int>::Cons &_args) -> bool {
                   if (_args.d_a0 == n) {
                     return true;
                   } else {
                     return local_mem(n, _args.d_a1);
                   }
                 }},
      l->v());
}
