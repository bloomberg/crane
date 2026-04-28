#ifndef INCLUDED_BCD_DIGIT_UPPER_BOUND
#define INCLUDED_BCD_DIGIT_UPPER_BOUND

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct BcdDigitUpperBound {
  __attribute__((pure)) static bool is_bcd_digitb(const unsigned int &n);
  static inline const unsigned int t =
      ((is_bcd_digitb(7u) ? 1u : 0u) + (is_bcd_digitb(12u) ? 1u : 0u));
};

#endif // INCLUDED_BCD_DIGIT_UPPER_BOUND
