#include "parallel.h"

uint64_t ParallelTest::ack(const std::pair<uint64_t, uint64_t> &p) {
  auto f_impl = [](auto &_self_f, uint64_t m, uint64_t n) -> uint64_t {
    auto ack_m_impl = [&](auto &_self_ack_m, uint64_t n0) -> uint64_t {
      if (m <= 0) {
        return (n0 + 1);
      } else {
        uint64_t pm = m - 1;
        if (n0 <= 0) {
          return _self_f(_self_f, pm, Nat::one);
        } else {
          uint64_t pn = n0 - 1;
          return _self_f(_self_f, pm, _self_ack_m(_self_ack_m, pn));
        }
      }
    };
    auto ack_m = [&](uint64_t n0) -> uint64_t {
      return ack_m_impl(ack_m_impl, n0);
    };
    return ack_m(n);
  };
  auto f = [&](uint64_t m, uint64_t n) -> uint64_t {
    return f_impl(f_impl, m, n);
  };
  return f(p.first, p.second);
}

std::pair<uint64_t, uint64_t> ParallelTest::fast(uint64_t m, uint64_t n) {
  std::pair<uint64_t, uint64_t> p = std::make_pair(m, n);
  std::future<uint64_t> t1 = std::async(std::launch::async, ack, p);
  std::future<uint64_t> t2 = std::async(std::launch::async, ack, p);
  uint64_t r1 = t1.get();
  uint64_t r2 = t2.get();
  return std::make_pair(r1, r2);
}

std::pair<uint64_t, uint64_t> ParallelTest::slow(uint64_t m, uint64_t n) {
  std::pair<uint64_t, uint64_t> p = std::make_pair(m, n);
  uint64_t r1 = ack(p);
  uint64_t r2 = ack(std::move(p));
  return std::make_pair(r1, r2);
}
