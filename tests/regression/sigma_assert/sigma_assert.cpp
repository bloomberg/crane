#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <sigma_assert.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int Nat::pred(const unsigned int n) {
  if (n <= 0) {
    return std::move(n);
  } else {
    unsigned int u = n - 1;
    return std::move(u);
  }
}

unsigned int Nat::div2(const unsigned int n) {
  if (n <= 0) {
    return 0;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n_ = n0 - 1;
      return (div2(n_) + 1);
    }
  }
}

unsigned int
SigmaAssert::safe_pred(const unsigned int n) { // Precondition: n != 0
  assert(n != 0);
  return Nat::pred(n);
}

unsigned int
SigmaAssert::safe_div2(const unsigned int n) { // Precondition: n >= 1
  assert(n >= 1);
  return Nat::div2(n);
}
