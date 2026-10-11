#include "type_family_constant_motive.h"

Comparison Nat::compare(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return Comparison::EQ;
    } else {
      uint64_t _x = m - 1;
      return Comparison::LT;
    }
  } else {
    uint64_t n_ = n - 1;
    if (m <= 0) {
      return Comparison::GT;
    } else {
      uint64_t m_ = m - 1;
      return compare(n_, m_);
    }
  }
}

bool Nat::Private_Dec::max_dec(uint64_t n, uint64_t m) {
  return max_case(
      n, m,
      [](uint64_t, uint64_t, bool h0) -> bool {
        if (h0) {
          return true;
        } else {
          return false;
        }
      },
      crane::obj(true), crane::obj(false));
}

bool Nat::max_dec(uint64_t x0_, uint64_t x1_) {
  return Private_Dec::max_dec(x0_, x1_);
}

bool TypeFamilyConstantMotive::larger_is_first(uint64_t n, uint64_t m) {
  return pick(
      n, m, [](uint64_t, uint64_t, bool b) { return b; }, crane::obj(true),
      crane::obj(false));
}

CompareSpecT Datatypes::CompareSpec2Type(Comparison c) {
  switch (c) {
  case Comparison::EQ: {
    return CompareSpecT::COMPEQT;
  }
  case Comparison::LT: {
    return CompareSpecT::COMPLTT;
  }
  case Comparison::GT: {
    return CompareSpecT::COMPGTT;
  }
  default:
    std::unreachable();
  }
}
