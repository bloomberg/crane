#include <bcd_digit_upper_bound.h>

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

__attribute__((pure)) bool
BcdDigitUpperBound::is_bcd_digitb(const unsigned int n) {
  return n <= 9u;
}
