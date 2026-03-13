#include <int63_arith.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) int64_t Int63Arith::i_abs(const int64_t x) {
  if (x < int64_t(0)) {
    return ((int64_t(0) - x) & 0x7FFFFFFFFFFFFFFFLL);
  } else {
    return x;
  }
}
