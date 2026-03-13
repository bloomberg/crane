#include <module.h>

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

__attribute__((pure)) Comparison NatOrdered::compare(const unsigned int _x0,
                                                     const unsigned int _x1) {
  return Nat::compare(_x0, _x1);
}

__attribute__((pure)) Comparison Nat::compare(const unsigned int n,
                                              const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return Comparison::e_EQ;
    } else {
      unsigned int _x = m - 1;
      return Comparison::e_LT;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return Comparison::e_GT;
    } else {
      unsigned int m_ = m - 1;
      return Nat::compare(n_, m_);
    }
  }
}
