#ifndef INCLUDED_SIGMA_ASSERT
#define INCLUDED_SIGMA_ASSERT

#include <cassert>

struct PeanoNat {
  static uint64_t div2(uint64_t n);
};

struct SigmaAssert {
  static uint64_t safe_pred(const uint64_t &n);
  static uint64_t safe_div2(const uint64_t &n);
  static inline const uint64_t test_pred = safe_pred(UINT64_C(5));
  static inline const uint64_t test_div2 = safe_div2(UINT64_C(4));
};

#endif // INCLUDED_SIGMA_ASSERT
