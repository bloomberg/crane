#include <let_fix.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
LetFix::local_sum(const std::shared_ptr<List<unsigned int>> &l) {
  std::function<unsigned int(unsigned int, std::shared_ptr<List<unsigned int>>)>
      go;
  go = [&](unsigned int acc,
           std::shared_ptr<List<unsigned int>> xs) -> unsigned int {
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) -> unsigned int {
              return std::move(acc);
            },
            [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
              unsigned int x = _args.d_a0;
              std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
              return go((std::move(acc) + std::move(x)), std::move(rest));
            }},
        xs->v());
  };
  return go(0u, l);
}

std::shared_ptr<List<unsigned int>> LetFix::local_flatten(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                 _args) -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::Nil_();
          },
          [](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                 _args) -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<List<unsigned int>> xs = _args.d_a0;
            std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest =
                _args.d_a1;
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<List<unsigned int>>)>
                inner;
            inner = [&](std::shared_ptr<List<unsigned int>> ys)
                -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               return local_flatten(rest);
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               unsigned int y = _args.d_a0;
                               std::shared_ptr<List<unsigned int>> ys_ =
                                   _args.d_a1;
                               return List<unsigned int>::ctor::Cons_(
                                   std::move(y), inner(std::move(ys_)));
                             }},
                  ys->v());
            };
            return inner(xs);
          }},
      xss->v());
}

__attribute__((pure)) bool
LetFix::local_mem(const unsigned int n,
                  const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil _args) -> bool {
                   return false;
                 },
                 [&](const typename List<unsigned int>::Cons _args) -> bool {
                   unsigned int x = _args.d_a0;
                   std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
                   if (std::move(x) == n) {
                     return true;
                   } else {
                     return local_mem(n, std::move(rest));
                   }
                 }},
      l->v());
}
