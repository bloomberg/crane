#include <bcd_digit_upper_bound.h>

#include <type_traits>

__attribute__((pure)) bool
BcdDigitUpperBound::is_bcd_digitb(const unsigned int &n) {
  return n <= 9u;
}
