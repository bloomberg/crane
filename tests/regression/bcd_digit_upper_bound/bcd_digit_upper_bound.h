#ifndef INCLUDED_BCD_DIGIT_UPPER_BOUND
#define INCLUDED_BCD_DIGIT_UPPER_BOUND

#include <cstdint>

struct BcdDigitUpperBound {
  static bool is_bcd_digitb(uint64_t n);
  static constexpr uint64_t t = UINT64_C(1);
};

#endif // INCLUDED_BCD_DIGIT_UPPER_BOUND
