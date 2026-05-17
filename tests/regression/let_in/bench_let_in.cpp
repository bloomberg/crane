#include "bench_let_in.h"

unsigned int BenchLetIn::swap_snd(unsigned int a, unsigned int b) {
  BenchLetIn::pair<unsigned int, unsigned int> p =
      pair<unsigned int, unsigned int>::pair0(a, b);
  auto &[a0, a1] = p;
  return a1;
}

unsigned int BenchLetIn::add_via_pair(unsigned int a, unsigned int b) {
  BenchLetIn::pair<unsigned int, unsigned int> p =
      pair<unsigned int, unsigned int>::pair0(a, b);
  auto &[a0, a1] = p;
  return (std::move(a0) + std::move(a1));
}

unsigned int BenchLetIn::nested_swap(unsigned int a, unsigned int b,
                                     unsigned int c, unsigned int d) {
  BenchLetIn::pair<unsigned int, unsigned int> p1 =
      pair<unsigned int, unsigned int>::pair0(a, b);
  BenchLetIn::pair<unsigned int, unsigned int> p2 =
      pair<unsigned int, unsigned int>::pair0(c, d);
  auto &[a0, a1] = p1;
  auto &[a00, a10] = p2;
  return (std::move(a0) + std::move(a10));
}

unsigned int BenchLetIn::sum_via_pairs(unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int m = n - 1;
    BenchLetIn::pair<unsigned int, unsigned int> p =
        pair<unsigned int, unsigned int>::pair0(n, m);
    auto &[a0, a1] = p;
    return (std::move(a0) + sum_via_pairs(std::move(a1)));
  }
}

unsigned int BenchLetIn::mid3(unsigned int a, unsigned int b, unsigned int c) {
  BenchLetIn::triple<unsigned int, unsigned int, unsigned int> t =
      triple<unsigned int, unsigned int, unsigned int>::triple0(a, b, c);
  auto &[a0, a1, a2] = t;
  return a1;
}

unsigned int BenchLetIn::sum3(unsigned int a, unsigned int b, unsigned int c) {
  BenchLetIn::triple<unsigned int, unsigned int, unsigned int> t =
      triple<unsigned int, unsigned int, unsigned int>::triple0(a, b, c);
  auto &[a0, a1, a2] = t;
  return (std::move(a0) + (std::move(a1) + std::move(a2)));
}

unsigned int BenchLetIn::chain_pairs(unsigned int a, unsigned int b,
                                     unsigned int c) {
  BenchLetIn::pair<unsigned int, unsigned int> p1 =
      pair<unsigned int, unsigned int>::pair0(a, b);
  auto &[a0, a1] = p1;
  BenchLetIn::pair<unsigned int, unsigned int> p2 =
      pair<unsigned int, unsigned int>::pair0(std::move(a0), c);
  auto &[a00, a10] = p2;
  return (std::move(a00) + std::move(a10));
}
