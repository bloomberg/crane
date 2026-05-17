#include "ack.h"

unsigned int Ack::ack(unsigned int m, unsigned int n) {
  auto ack_m_impl = [&](auto &_self_ack_m, unsigned int n0) -> unsigned int {
    if (m <= 0) {
      return (n0 + 1);
    } else {
      unsigned int pm = m - 1;
      if (n0 <= 0) {
        return ack(pm, Nat::one);
      } else {
        unsigned int pn = n0 - 1;
        return ack(pm, _self_ack_m(_self_ack_m, pn));
      }
    }
  };
  auto ack_m = [&](unsigned int n0) -> unsigned int {
    return ack_m_impl(ack_m_impl, n0);
  };
  return ack_m(n);
}
