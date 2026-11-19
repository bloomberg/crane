#include "native_number_compare.h"

/// compare and eq_dec on numbers mapped to machine integers become
/// native comparisons.  The structural versions count both arguments down
/// to zero, so the large values in the test would take hours (compare)
/// or overflow the stack (eq_dec).
uint64_t NativeNumberCompare::code(Comparison c) {
  switch (c) {
  case Comparison::EQ: {
    return UINT64_C(1);
  }
  case Comparison::LT: {
    return UINT64_C(0);
  }
  case Comparison::GT: {
    return UINT64_C(2);
  }
  default:
    std::unreachable();
  }
}

uint64_t NativeNumberCompare::nat_cmp(uint64_t a, uint64_t b) {
  return code(
      (a < b ? Comparison::LT : (b < a ? Comparison::GT : Comparison::EQ)));
}

uint64_t NativeNumberCompare::nat_cmp_(uint64_t a, uint64_t b) {
  return nat_cmp(a, b);
}

bool NativeNumberCompare::nat_dec(uint64_t a, uint64_t b) {
  if (a == b) {
    return true;
  } else {
    return false;
  }
}

uint64_t NativeNumberCompare::n_cmp(unsigned int a, unsigned int b) {
  return code(
      (a < b ? Comparison::LT : (b < a ? Comparison::GT : Comparison::EQ)));
}

bool NativeNumberCompare::n_dec(unsigned int a, unsigned int b) {
  if (a == b) {
    return true;
  } else {
    return false;
  }
}

uint64_t NativeNumberCompare::pos_cmp(unsigned int a, unsigned int b) {
  return code(
      (a < b ? Comparison::LT : (b < a ? Comparison::GT : Comparison::EQ)));
}

bool NativeNumberCompare::pos_dec(unsigned int a, unsigned int b) {
  if (a == b) {
    return true;
  } else {
    return false;
  }
}

uint64_t NativeNumberCompare::z_cmp(int64_t a, int64_t b) {
  return code(
      (a < b ? Comparison::LT : (b < a ? Comparison::GT : Comparison::EQ)));
}

bool NativeNumberCompare::z_dec(int64_t a, int64_t b) {
  if (a == b) {
    return true;
  } else {
    return false;
  }
}

uint64_t NativeNumberCompare::nat_cmp_value(uint64_t a, uint64_t b) {
  return apply_cmp([](uint64_t _x0,
                      uint64_t _x1)
                        -> Comparison {
    return (_x0 < _x1 ? Comparison::LT
                      : (_x1 < _x0 ? Comparison::GT : Comparison::EQ));
  },
                   a, b);
}
