#include "bench_let_in.h"

uint64_t BenchLetIn::swap_snd(uint64_t a, uint64_t b) {
  BenchLetIn::pair<uint64_t, uint64_t> p =
      pair<uint64_t, uint64_t>::pair0(a, b);
  auto &[a0, a1] = p;
  return a1;
}

uint64_t BenchLetIn::add_via_pair(uint64_t a, uint64_t b) {
  BenchLetIn::pair<uint64_t, uint64_t> p =
      pair<uint64_t, uint64_t>::pair0(a, b);
  auto &[a0, a1] = p;
  return (std::move(a0) + std::move(a1));
}

uint64_t BenchLetIn::nested_swap(uint64_t a, uint64_t b, uint64_t c,
                                 uint64_t d) {
  BenchLetIn::pair<uint64_t, uint64_t> p1 =
      pair<uint64_t, uint64_t>::pair0(a, b);
  BenchLetIn::pair<uint64_t, uint64_t> p2 =
      pair<uint64_t, uint64_t>::pair0(c, d);
  auto &[a0, a1] = p1;
  auto &[a00, a10] = p2;
  return (std::move(a0) + std::move(a10));
}

uint64_t BenchLetIn::sum_via_pairs(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    BenchLetIn::pair<uint64_t, uint64_t> p =
        pair<uint64_t, uint64_t>::pair0(n, m);
    auto &[a0, a1] = p;
    return (std::move(a0) + sum_via_pairs(std::move(a1)));
  }
}

uint64_t BenchLetIn::mid3(uint64_t a, uint64_t b, uint64_t c) {
  BenchLetIn::triple<uint64_t, uint64_t, uint64_t> t =
      triple<uint64_t, uint64_t, uint64_t>::triple0(a, b, c);
  auto &[a0, a1, a2] = t;
  return a1;
}

uint64_t BenchLetIn::sum3(uint64_t a, uint64_t b, uint64_t c) {
  BenchLetIn::triple<uint64_t, uint64_t, uint64_t> t =
      triple<uint64_t, uint64_t, uint64_t>::triple0(a, b, c);
  auto &[a0, a1, a2] = t;
  return (std::move(a0) + (std::move(a1) + std::move(a2)));
}

uint64_t BenchLetIn::chain_pairs(uint64_t a, uint64_t b, uint64_t c) {
  BenchLetIn::pair<uint64_t, uint64_t> p1 =
      pair<uint64_t, uint64_t>::pair0(a, b);
  auto &[a0, a1] = p1;
  BenchLetIn::pair<uint64_t, uint64_t> p2 =
      pair<uint64_t, uint64_t>::pair0(std::move(a0), c);
  auto &[a00, a10] = p2;
  return (std::move(a00) + std::move(a10));
}
