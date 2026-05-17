#include "module.h"

Comparison NatOrdered::compare(unsigned int _x0, unsigned int _x1) {
  return Nat::compare(_x0, _x1);
}

Comparison Nat::compare(unsigned int n, unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return Comparison::EQ;
    } else {
      unsigned int _x = m - 1;
      return Comparison::LT;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return Comparison::GT;
    } else {
      unsigned int m_ = m - 1;
      return Nat::compare(n_, m_);
    }
  }
}
