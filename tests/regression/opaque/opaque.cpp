#include <opaque.h>

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

__attribute__((pure)) unsigned int Opaque::safe_pred(const unsigned int n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    unsigned int n0 = n - 1;
    return n0;
  }
}

__attribute__((pure)) unsigned int Opaque::pred_of_succ(const unsigned int n) {
  return safe_pred((std::move(n) + 1));
}

__attribute__((pure)) bool Opaque::nat_eq_dec(const unsigned int n,
                                              const unsigned int x) {
  if (n <= 0) {
    if (x <= 0) {
      return true;
    } else {
      unsigned int _x = x - 1;
      return false;
    }
  } else {
    unsigned int n0 = n - 1;
    if (x <= 0) {
      return false;
    } else {
      unsigned int n1 = x - 1;
      if (nat_eq_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

__attribute__((pure)) bool Opaque::are_equal(const unsigned int n,
                                             const unsigned int m) {
  if (nat_eq_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

std::shared_ptr<Sig<unsigned int>> Opaque::bounded_add(const unsigned int _x0,
                                                       const unsigned int _x1,
                                                       const unsigned int _x2) {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.opaque.Opaque.Opaque.bounded_add");
}
