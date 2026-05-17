#include "opaque.h"

uint64_t Opaque::safe_pred(uint64_t n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    uint64_t n0 = n - 1;
    return n0;
  }
}

uint64_t Opaque::pred_of_succ(uint64_t n) { return safe_pred((n + 1)); }

bool Opaque::nat_eq_dec(uint64_t n, uint64_t x) {
  if (n <= 0) {
    if (x <= 0) {
      return true;
    } else {
      uint64_t _x = x - 1;
      return false;
    }
  } else {
    uint64_t n0 = n - 1;
    if (x <= 0) {
      return false;
    } else {
      uint64_t n1 = x - 1;
      if (nat_eq_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool Opaque::are_equal(uint64_t n, uint64_t m) {
  if (nat_eq_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

Sig<uint64_t> Opaque::bounded_add(uint64_t, uint64_t, uint64_t) {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.opaque.Opaque.Opaque.bounded_add");
}
