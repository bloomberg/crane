#ifndef INCLUDED_BCD_DIGIT_UPPER_BOUND
#define INCLUDED_BCD_DIGIT_UPPER_BOUND

struct BcdDigitUpperBound {
  static bool is_bcd_digitb(uint64_t n);
  static inline const uint64_t t =
      ((is_bcd_digitb(UINT64_C(7)) ? UINT64_C(1) : UINT64_C(0)) +
       (is_bcd_digitb(UINT64_C(12)) ? UINT64_C(1) : UINT64_C(0)));
};

#endif // INCLUDED_BCD_DIGIT_UPPER_BOUND
