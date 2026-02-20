#include <algorithm>
#include <any>
#include <bench_let_in.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int BenchLetIn::swap_snd(const unsigned int a, const unsigned int b) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
      pair<unsigned int, unsigned int>::ctor::Pair_uptr(a, b);
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::pair<unsigned int, unsigned int>::Pair
                 _args) -> unsigned int {
            unsigned int y = _args._a1;
            return y;
          }},
      p->v());
}

unsigned int BenchLetIn::add_via_pair(const unsigned int a,
                                      const unsigned int b) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
      pair<unsigned int, unsigned int>::ctor::Pair_uptr(a, b);
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::pair<unsigned int, unsigned int>::Pair
                 _args) -> unsigned int {
            unsigned int x = _args._a0;
            unsigned int y = _args._a1;
            return (x + y);
          }},
      p->v());
}

unsigned int BenchLetIn::nested_swap(const unsigned int a, const unsigned int b,
                                     const unsigned int c,
                                     const unsigned int d) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p1 =
      pair<unsigned int, unsigned int>::ctor::Pair_uptr(a, b);
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p2 =
      pair<unsigned int, unsigned int>::ctor::Pair_uptr(c, d);
  return std::visit(
      Overloaded{[&](const typename BenchLetIn::pair<
                     unsigned int, unsigned int>::Pair _args) -> unsigned int {
        unsigned int x = _args._a0;
        return std::visit(
            Overloaded{
                [&](const typename BenchLetIn::pair<
                    unsigned int, unsigned int>::Pair _args) -> unsigned int {
                  unsigned int w = _args._a1;
                  return (x + w);
                }},
            p2->v());
      }},
      p1->v());
}

unsigned int BenchLetIn::sum_via_pairs(const unsigned int n) {
  if (n <= 0) {
    return 0;
  } else {
    unsigned int m = n - 1;
    std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
        pair<unsigned int, unsigned int>::ctor::Pair_uptr(n, m);
    return std::visit(
        Overloaded{
            [](const typename BenchLetIn::pair<unsigned int, unsigned int>::Pair
                   _args) -> unsigned int {
              unsigned int x = _args._a0;
              unsigned int y = _args._a1;
              return (x + sum_via_pairs(y));
            }},
        p->v());
  }
}

unsigned int BenchLetIn::mid3(const unsigned int a, const unsigned int b,
                              const unsigned int c) {
  std::unique_ptr<BenchLetIn::triple<unsigned int, unsigned int, unsigned int>>
      t = triple<unsigned int, unsigned int, unsigned int>::ctor::Triple_uptr(
          a, b, c);
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::triple<unsigned int, unsigned int,
                                               unsigned int>::Triple _args)
              -> unsigned int {
            unsigned int y = _args._a1;
            return y;
          }},
      t->v());
}

unsigned int BenchLetIn::sum3(const unsigned int a, const unsigned int b,
                              const unsigned int c) {
  std::unique_ptr<BenchLetIn::triple<unsigned int, unsigned int, unsigned int>>
      t = triple<unsigned int, unsigned int, unsigned int>::ctor::Triple_uptr(
          a, b, c);
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::triple<unsigned int, unsigned int,
                                               unsigned int>::Triple _args)
              -> unsigned int {
            unsigned int x = _args._a0;
            unsigned int y = _args._a1;
            unsigned int z = _args._a2;
            return (x + (y + z));
          }},
      t->v());
}

unsigned int BenchLetIn::chain_pairs(const unsigned int a, const unsigned int b,
                                     const unsigned int c) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p1 =
      pair<unsigned int, unsigned int>::ctor::Pair_uptr(a, b);
  return std::visit(
      Overloaded{[&](const typename BenchLetIn::pair<
                     unsigned int, unsigned int>::Pair _args) -> unsigned int {
        unsigned int x = _args._a0;
        std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p2 =
            pair<unsigned int, unsigned int>::ctor::Pair_uptr(x, c);
        return std::visit(
            Overloaded{
                [](const typename BenchLetIn::pair<
                    unsigned int, unsigned int>::Pair _args) -> unsigned int {
                  unsigned int u = _args._a0;
                  unsigned int v = _args._a1;
                  return (u + v);
                }},
            p2->v());
      }},
      p1->v());
}
