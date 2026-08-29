#include "sigma_assert.h"

uint64_t PeanoNat::div2(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n_ = n0 - 1;
      return (PeanoNat::div2(n_) + 1);
    }
  }
}

uint64_t SigmaAssert::safe_pred(const uint64_t &n) { // Precondition: n != 0
  assert(n != 0);
  return (n ? n - 1 : n);
}

uint64_t SigmaAssert::safe_div2(const uint64_t &n) { // Precondition: n >= 1
  assert(n >= 1);
  return PeanoNat::div2(n);
}
