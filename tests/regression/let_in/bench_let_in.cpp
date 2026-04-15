#include <bench_let_in.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int BenchLetIn::swap_snd(const unsigned int a,
                                                        const unsigned int b) {
  std::shared_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
      pair<unsigned int, unsigned int>::pair0(a, b);
  const auto &_m = *std::get_if<
      typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(&p->v());
  return _m.d_a1;
}

__attribute__((pure)) unsigned int
BenchLetIn::add_via_pair(const unsigned int a, const unsigned int b) {
  std::shared_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
      pair<unsigned int, unsigned int>::pair0(a, b);
  const auto &_m = *std::get_if<
      typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(&p->v());
  return (_m.d_a0 + _m.d_a1);
}

__attribute__((pure)) unsigned int
BenchLetIn::nested_swap(const unsigned int a, const unsigned int b,
                        const unsigned int c, const unsigned int d) {
  std::shared_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p1 =
      pair<unsigned int, unsigned int>::pair0(a, b);
  std::shared_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p2 =
      pair<unsigned int, unsigned int>::pair0(c, d);
  const auto &_m = *std::get_if<
      typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(&p1->v());
  const auto &_m0 = *std::get_if<
      typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(&p2->v());
  return (_m.d_a0 + _m0.d_a1);
}

__attribute__((pure)) unsigned int
BenchLetIn::sum_via_pairs(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int m = n - 1;
    std::shared_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p =
        pair<unsigned int, unsigned int>::pair0(n, m);
    const auto &_m = *std::get_if<
        typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(&p->v());
    return (_m.d_a0 + sum_via_pairs(_m.d_a1));
  }
}

__attribute__((pure)) unsigned int BenchLetIn::mid3(const unsigned int a,
                                                    const unsigned int b,
                                                    const unsigned int c) {
  std::shared_ptr<BenchLetIn::triple<unsigned int, unsigned int, unsigned int>>
      t = triple<unsigned int, unsigned int, unsigned int>::triple0(a, b, c);
  const auto &_m =
      *std::get_if<typename BenchLetIn::triple<unsigned int, unsigned int,
                                               unsigned int>::Triple0>(&t->v());
  return _m.d_a1;
}

__attribute__((pure)) unsigned int BenchLetIn::sum3(const unsigned int a,
                                                    const unsigned int b,
                                                    const unsigned int c) {
  std::shared_ptr<BenchLetIn::triple<unsigned int, unsigned int, unsigned int>>
      t = triple<unsigned int, unsigned int, unsigned int>::triple0(a, b, c);
  const auto &_m =
      *std::get_if<typename BenchLetIn::triple<unsigned int, unsigned int,
                                               unsigned int>::Triple0>(&t->v());
  return (_m.d_a0 + (_m.d_a1 + _m.d_a2));
}

__attribute__((pure)) unsigned int
BenchLetIn::chain_pairs(const unsigned int a, const unsigned int b,
                        const unsigned int c) {
  std::shared_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p1 =
      pair<unsigned int, unsigned int>::pair0(a, b);
  const auto &_m = *std::get_if<
      typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(&p1->v());
  std::shared_ptr<BenchLetIn::pair<unsigned int, unsigned int>> p2 =
      pair<unsigned int, unsigned int>::pair0(_m.d_a0, c);
  const auto &_m0 = *std::get_if<
      typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(&p2->v());
  return (_m0.d_a0 + _m0.d_a1);
}
