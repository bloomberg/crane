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
      pair<unsigned int, unsigned int>::pair0_uptr(std::move(a), std::move(b));
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0
                 _args) -> unsigned int { return _args.d_a1; }},
      std::move(p)->v());
}

__attribute__((pure)) unsigned int
BenchLetIn::add_via_pair(const unsigned int a, const unsigned int b) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
      pair<unsigned int, unsigned int>::pair0_uptr(std::move(a), std::move(b));
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0
                 _args) -> unsigned int { return (_args.d_a0 + _args.d_a1); }},
      std::move(p)->v());
}

__attribute__((pure)) unsigned int
BenchLetIn::nested_swap(const unsigned int a, const unsigned int b,
                        const unsigned int c, const unsigned int d) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p1 =
      pair<unsigned int, unsigned int>::pair0_uptr(std::move(a), std::move(b));
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p2 =
      pair<unsigned int, unsigned int>::pair0_uptr(std::move(c), std::move(d));
  return std::visit(
      Overloaded{[&](const typename BenchLetIn::pair<
                     unsigned int, unsigned int>::Pair0 _args) -> unsigned int {
        return std::visit(
            Overloaded{
                [&](const typename BenchLetIn::pair<unsigned int,
                                                    unsigned int>::Pair0 _args0)
                    -> unsigned int { return (_args.d_a0 + _args0.d_a1); }},
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
        pair<unsigned int, unsigned int>::pair0_uptr(n, std::move(m));
    return std::visit(
        Overloaded{
            [](const typename BenchLetIn::pair<
                unsigned int, unsigned int>::Pair0 _args) -> unsigned int {
              return (_args.d_a0 + sum_via_pairs(_args.d_a1));
            }},
        std::move(p)->v());
  }
}

__attribute__((pure)) unsigned int BenchLetIn::mid3(const unsigned int a,
                                                    const unsigned int b,
                                                    const unsigned int c) {
  std::unique_ptr<BenchLetIn::triple<unsigned int, unsigned int, unsigned int>>
      t = triple<unsigned int, unsigned int, unsigned int>::triple0_uptr(
          std::move(a), std::move(b), std::move(c));
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::triple<unsigned int, unsigned int,
                                               unsigned int>::Triple0 _args)
              -> unsigned int { return _args.d_a1; }},
      std::move(t)->v());
}

__attribute__((pure)) unsigned int BenchLetIn::sum3(const unsigned int a,
                                                    const unsigned int b,
                                                    const unsigned int c) {
  std::unique_ptr<BenchLetIn::triple<unsigned int, unsigned int, unsigned int>>
      t = triple<unsigned int, unsigned int, unsigned int>::triple0_uptr(
          std::move(a), std::move(b), std::move(c));
  return std::visit(
      Overloaded{
          [](const typename BenchLetIn::triple<unsigned int, unsigned int,
                                               unsigned int>::Triple0 _args)
              -> unsigned int {
            return (_args.d_a0 + (_args.d_a1 + _args.d_a2));
          }},
      std::move(t)->v());
}

__attribute__((pure)) unsigned int
BenchLetIn::chain_pairs(const unsigned int a, const unsigned int b,
                        const unsigned int c) {
  std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p1 =
      pair<unsigned int, unsigned int>::pair0_uptr(std::move(a), std::move(b));
  return std::visit(
      Overloaded{[&](const typename BenchLetIn::pair<
                     unsigned int, unsigned int>::Pair0 _args) -> unsigned int {
        std::unique_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p2 =
            pair<unsigned int, unsigned int>::pair0_uptr(_args.d_a0,
                                                         std::move(c));
        return std::visit(
            Overloaded{
                [](const typename BenchLetIn::pair<unsigned int,
                                                   unsigned int>::Pair0 _args0)
                    -> unsigned int { return (_args0.d_a0 + _args0.d_a1); }},
            std::move(p2)->v());
      }},
      std::move(p1)->v());
}
