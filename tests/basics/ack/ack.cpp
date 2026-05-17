#include "ack.h"

uint64_t Ack::ack(uint64_t m, uint64_t n) {
  auto ack_m_impl = [&](auto &_self_ack_m, uint64_t n0) -> uint64_t {
    if (m <= 0) {
      return (n0 + 1);
    } else {
      uint64_t pm = m - 1;
      if (n0 <= 0) {
        return ack(pm, Nat::one);
      } else {
        uint64_t pn = n0 - 1;
        return ack(pm, _self_ack_m(_self_ack_m, pn));
      }
    }
  };
  auto ack_m = [&](uint64_t n0) -> uint64_t {
    return ack_m_impl(ack_m_impl, n0);
  };
  return ack_m(n);
}
