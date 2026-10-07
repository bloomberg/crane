#include "erased_let_not_result_type.h"

bool Nat::eq_dec(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      uint64_t _x = m - 1;
      return false;
    }
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      uint64_t n1 = m - 1;
      bool s = eq_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

ErasedLetNotResultType::Syms::semty
ErasedLetNotResultType::Syms::cast(uint64_t, uint64_t,
                                   ErasedLetNotResultType::Syms::semty v) {
  return v;
}

ErasedLetNotResultType::Syms::semty
ErasedLetNotResultType::Syms::default_(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t m = n - 1;
    return m;
  }
}

uint64_t
ErasedLetNotResultType::Syms::size(uint64_t n,
                                   ErasedLetNotResultType::Syms::semty b) {
  if (n <= 0) {
    if (crane::any_cast<bool>(b)) {
      return UINT64_C(1);
    } else {
      return UINT64_C(0);
    }
  } else {
    uint64_t _x = n - 1;
    return crane::any_cast<uint64_t>(b);
  }
}
