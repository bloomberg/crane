#include <bench_let_in.h>

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

__attribute__((pure)) unsigned int BenchLetIn::swap_snd(const unsigned int a,
                                                        const unsigned int b) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
      pair<unsigned int, unsigned int>::ctor::Pair0_uptr(std::move(a),
                                                         std::move(b));
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0
                 _args) -> unsigned int {
            unsigned int y = _args.d_a1;
            return std::move(y);
          }},
      std::move(p)->v());
}

__attribute__((pure)) unsigned int
BenchLetIn::add_via_pair(const unsigned int a, const unsigned int b) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
      pair<unsigned int, unsigned int>::ctor::Pair0_uptr(std::move(a),
                                                         std::move(b));
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0
                 _args) -> unsigned int {
            unsigned int x = _args.d_a0;
            unsigned int y = _args.d_a1;
            return (std::move(x) + std::move(y));
          }},
      std::move(p)->v());
}

__attribute__((pure)) unsigned int
BenchLetIn::nested_swap(const unsigned int a, const unsigned int b,
                        const unsigned int c, const unsigned int d) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p1 =
      pair<unsigned int, unsigned int>::ctor::Pair0_uptr(std::move(a),
                                                         std::move(b));
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p2 =
      pair<unsigned int, unsigned int>::ctor::Pair0_uptr(std::move(c),
                                                         std::move(d));
  return std::visit(
      Overloaded{[&](const typename BenchLetIn::pair<
                     unsigned int, unsigned int>::Pair0 _args) -> unsigned int {
        unsigned int x = _args.d_a0;
        return std::visit(
            Overloaded{
                [&](const typename BenchLetIn::pair<
                    unsigned int, unsigned int>::Pair0 _args) -> unsigned int {
                  unsigned int w = _args.d_a1;
                  return (std::move(x) + std::move(w));
                }},
            std::move(p2)->v());
      }},
      std::move(p1)->v());
}

__attribute__((pure)) unsigned int
BenchLetIn::sum_via_pairs(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int m = n - 1;
    std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
        pair<unsigned int, unsigned int>::ctor::Pair0_uptr(n, std::move(m));
    return std::visit(
        Overloaded{
            [](const typename BenchLetIn::pair<
                unsigned int, unsigned int>::Pair0 _args) -> unsigned int {
              unsigned int x = _args.d_a0;
              unsigned int y = _args.d_a1;
              return (std::move(x) + sum_via_pairs(std::move(y)));
            }},
        std::move(p)->v());
  }
}

__attribute__((pure)) unsigned int BenchLetIn::mid3(const unsigned int a,
                                                    const unsigned int b,
                                                    const unsigned int c) {
  std::unique_ptr<BenchLetIn::triple<unsigned int, unsigned int, unsigned int>>
      t = triple<unsigned int, unsigned int, unsigned int>::ctor::Triple0_uptr(
          std::move(a), std::move(b), std::move(c));
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::triple<unsigned int, unsigned int,
                                               unsigned int>::Triple0 _args)
              -> unsigned int {
            unsigned int y = _args.d_a1;
            return std::move(y);
          }},
      std::move(t)->v());
}

__attribute__((pure)) unsigned int BenchLetIn::sum3(const unsigned int a,
                                                    const unsigned int b,
                                                    const unsigned int c) {
  std::unique_ptr<BenchLetIn::triple<unsigned int, unsigned int, unsigned int>>
      t = triple<unsigned int, unsigned int, unsigned int>::ctor::Triple0_uptr(
          std::move(a), std::move(b), std::move(c));
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::triple<unsigned int, unsigned int,
                                               unsigned int>::Triple0 _args)
              -> unsigned int {
            unsigned int x = _args.d_a0;
            unsigned int y = _args.d_a1;
            unsigned int z = _args.d_a2;
            return (std::move(x) + (std::move(y) + std::move(z)));
          }},
      std::move(t)->v());
}

__attribute__((pure)) unsigned int
BenchLetIn::chain_pairs(const unsigned int a, const unsigned int b,
                        const unsigned int c) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p1 =
      pair<unsigned int, unsigned int>::ctor::Pair0_uptr(std::move(a),
                                                         std::move(b));
  return std::visit(
      Overloaded{[&](const typename BenchLetIn::pair<
                     unsigned int, unsigned int>::Pair0 _args) -> unsigned int {
        unsigned int x = _args.d_a0;
        std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p2 =
            pair<unsigned int, unsigned int>::ctor::Pair0_uptr(std::move(x),
                                                               std::move(c));
        return std::visit(
            Overloaded{
                [](const typename BenchLetIn::pair<
                    unsigned int, unsigned int>::Pair0 _args) -> unsigned int {
                  unsigned int u = _args.d_a0;
                  unsigned int v = _args.d_a1;
                  return (std::move(u) + std::move(v));
                }},
            std::move(p2)->v());
      }},
      std::move(p1)->v());
}
