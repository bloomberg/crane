#include <bench_let_in.h>

unsigned int BenchLetIn::swap_snd(unsigned int a, unsigned int b) {
  BenchLetIn::pair<unsigned int, unsigned int> p =
      pair<unsigned int, unsigned int>::pair0(a, b);
  auto &[d_a0, d_a1] =
      std::get<typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(
          p.v_mut());
  return d_a1;
}

unsigned int BenchLetIn::add_via_pair(unsigned int a, unsigned int b) {
  BenchLetIn::pair<unsigned int, unsigned int> p =
      pair<unsigned int, unsigned int>::pair0(a, b);
  auto &[d_a0, d_a1] =
      std::get<typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(
          p.v_mut());
  return (d_a0 + d_a1);
}

unsigned int BenchLetIn::nested_swap(unsigned int a, unsigned int b,
                                     unsigned int c, unsigned int d) {
  BenchLetIn::pair<unsigned int, unsigned int> p1 =
      pair<unsigned int, unsigned int>::pair0(a, b);
  BenchLetIn::pair<unsigned int, unsigned int> p2 =
      pair<unsigned int, unsigned int>::pair0(c, d);
  auto &[d_a0, d_a1] =
      std::get<typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(
          p1.v_mut());
  auto &[d_a00, d_a10] =
      std::get<typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(
          p2.v_mut());
  return (d_a0 + d_a10);
}

unsigned int BenchLetIn::sum_via_pairs(unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int m = n - 1;
    BenchLetIn::pair<unsigned int, unsigned int> p =
        pair<unsigned int, unsigned int>::pair0(n, m);
    auto &[d_a0, d_a1] =
        std::get<typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(
            p.v_mut());
    return (d_a0 + sum_via_pairs(d_a1));
  }
}

unsigned int BenchLetIn::mid3(unsigned int a, unsigned int b, unsigned int c) {
  BenchLetIn::triple<unsigned int, unsigned int, unsigned int> t =
      triple<unsigned int, unsigned int, unsigned int>::triple0(a, b, c);
  auto &[d_a0, d_a1, d_a2] =
      std::get<typename BenchLetIn::triple<unsigned int, unsigned int,
                                           unsigned int>::Triple0>(t.v_mut());
  return d_a1;
}

unsigned int BenchLetIn::sum3(unsigned int a, unsigned int b, unsigned int c) {
  BenchLetIn::triple<unsigned int, unsigned int, unsigned int> t =
      triple<unsigned int, unsigned int, unsigned int>::triple0(a, b, c);
  auto &[d_a0, d_a1, d_a2] =
      std::get<typename BenchLetIn::triple<unsigned int, unsigned int,
                                           unsigned int>::Triple0>(t.v_mut());
  return (d_a0 + (d_a1 + d_a2));
}

unsigned int BenchLetIn::chain_pairs(unsigned int a, unsigned int b,
                                     unsigned int c) {
  BenchLetIn::pair<unsigned int, unsigned int> p1 =
      pair<unsigned int, unsigned int>::pair0(a, b);
  auto &[d_a0, d_a1] =
      std::get<typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(
          p1.v_mut());
  BenchLetIn::pair<unsigned int, unsigned int> p2 =
      pair<unsigned int, unsigned int>::pair0(d_a0, c);
  auto &[d_a00, d_a10] =
      std::get<typename BenchLetIn::pair<unsigned int, unsigned int>::Pair0>(
          p2.v_mut());
  return (d_a00 + d_a10);
}
