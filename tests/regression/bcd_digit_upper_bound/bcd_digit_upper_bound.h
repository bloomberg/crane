#ifndef INCLUDED_BCD_DIGIT_UPPER_BOUND
#define INCLUDED_BCD_DIGIT_UPPER_BOUND

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct BcdDigitUpperBound {
  __attribute__((pure)) static bool is_bcd_digitb(const unsigned int n);
  static inline const unsigned int t = ([](void) {
    if (is_bcd_digitb(7u)) {
      return 1u;
    } else {
      return 0u;
    }
  }() +
                                        [](void) {
                                          if (is_bcd_digitb(12u)) {
                                            return 1u;
                                          } else {
                                            return 0u;
                                          }
                                        }());
};

#endif // INCLUDED_BCD_DIGIT_UPPER_BOUND
