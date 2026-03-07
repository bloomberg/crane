#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nibble_wrap_plus_19.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int NibbleWrapPlus19::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}
