#include "error_failwith.h"

uint64_t ErrorFailwith::safe_div(uint64_t a, uint64_t b) {
  if (b == UINT64_C(0)) {
    return [&]() -> uint64_t {
      throw std::runtime_error(std::string("div by zero"));
    }();
  } else {
    return (b ? a / b : 0);
  }
}

uint64_t ErrorFailwith::result() { return safe_div(UINT64_C(10), UINT64_C(2)); }
