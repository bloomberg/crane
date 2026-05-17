#include "module.h"

Comparison NatOrdered::compare(uint64_t _x0, uint64_t _x1) {
  return Nat::compare(_x0, _x1);
}

Comparison Nat::compare(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return Comparison::EQ;
    } else {
      uint64_t _x = m - 1;
      return Comparison::LT;
    }
  } else {
    uint64_t n_ = n - 1;
    if (m <= 0) {
      return Comparison::GT;
    } else {
      uint64_t m_ = m - 1;
      return Nat::compare(n_, m_);
    }
  }
}
