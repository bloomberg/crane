#ifndef INCLUDED_BCD_DIGIT_UPPER_BOUND
#define INCLUDED_BCD_DIGIT_UPPER_BOUND

struct BcdDigitUpperBound {
  static bool is_bcd_digitb(unsigned int n);
  static inline const unsigned int t =
      ((is_bcd_digitb(7u) ? 1u : 0u) + (is_bcd_digitb(12u) ? 1u : 0u));
};

#endif // INCLUDED_BCD_DIGIT_UPPER_BOUND
