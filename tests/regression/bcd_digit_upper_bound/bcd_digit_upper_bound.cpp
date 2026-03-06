#include <algorithm>
#include <any>
#include <bcd_digit_upper_bound.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

bool BcdDigitUpperBound::is_bcd_digitb(const unsigned int n) {
  return (n <= (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
}
