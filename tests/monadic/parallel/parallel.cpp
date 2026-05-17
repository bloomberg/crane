#include "parallel.h"

unsigned int ParallelTest::ack(const std::pair<unsigned int, unsigned int> &p) {
  auto f_impl = [](auto &_self_f, unsigned int m,
                   unsigned int n) -> unsigned int {
    auto ack_m_impl = [&](auto &_self_ack_m, unsigned int n0) -> unsigned int {
      if (m <= 0) {
        return (n0 + 1);
      } else {
        unsigned int pm = m - 1;
        if (n0 <= 0) {
          return _self_f(_self_f, pm, Nat::one);
        } else {
          unsigned int pn = n0 - 1;
          return _self_f(_self_f, pm, _self_ack_m(_self_ack_m, pn));
        }
      }
    };
    auto ack_m = [&](unsigned int n0) -> unsigned int {
      return ack_m_impl(ack_m_impl, n0);
    };
    return ack_m(n);
  };
  auto f = [&](unsigned int m, unsigned int n) -> unsigned int {
    return f_impl(f_impl, m, n);
  };
  return f(p.first, p.second);
}

std::pair<unsigned int, unsigned int> ParallelTest::fast(unsigned int m,
                                                         unsigned int n) {
  std::pair<unsigned int, unsigned int> p = std::make_pair(m, n);
  std::future<unsigned int> t1 = std::async(std::launch::async, ack, p);
  std::future<unsigned int> t2 = std::async(std::launch::async, ack, p);
  unsigned int r1 = t1.get();
  unsigned int r2 = t2.get();
  return std::make_pair(r1, r2);
}

std::pair<unsigned int, unsigned int> ParallelTest::slow(unsigned int m,
                                                         unsigned int n) {
  std::pair<unsigned int, unsigned int> p = std::make_pair(m, n);
  unsigned int r1 = ack(p);
  unsigned int r2 = ack(p);
  return std::make_pair(r1, r2);
}
