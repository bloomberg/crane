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

comparison NatOrdered::compare(const unsigned int _x0, const unsigned int _x1) {
  return Nat::compare(_x0, _x1);
}

comparison Nat::compare(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return comparison::Eq;
    } else {
      unsigned int _x = m - 1;
      return comparison::Lt;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return comparison::Gt;
    } else {
      unsigned int m_ = m - 1;
      return Nat::compare(n_, m_);
    }
  }
}
