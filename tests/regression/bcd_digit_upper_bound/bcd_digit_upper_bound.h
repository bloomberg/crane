#ifndef INCLUDED_BCD_DIGIT_UPPER_BOUND
#define INCLUDED_BCD_DIGIT_UPPER_BOUND

#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct BcdDigitUpperBound {
  __attribute__((pure)) static bool is_bcd_digitb(const unsigned int n);
  static inline const unsigned int t = ([]() -> unsigned int {
    if (is_bcd_digitb(7u)) {
      return 1u;
    } else {
      return 0u;
    }
  }() + []() -> unsigned int {
    if (is_bcd_digitb(12u)) {
      return 1u;
    } else {
      return 0u;
    }
  }());
};

#endif // INCLUDED_BCD_DIGIT_UPPER_BOUND
