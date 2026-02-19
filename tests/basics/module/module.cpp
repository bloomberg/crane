#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <module.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

comparison compare(const unsigned int n, const unsigned int m) {
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
      return compare(n_, m_);
    }
  }
}

comparison NatOrdered::compare(const unsigned int _x0, const unsigned int _x1) {
  return ::compare(_x0, _x1);
}
