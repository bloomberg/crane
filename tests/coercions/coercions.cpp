#include "coercions.h"

uint64_t Coercions::bool_to_nat(bool b) {
  if (b) {
    return UINT64_C(1);
  } else {
    return UINT64_C(0);
  }
}

uint64_t Coercions::add_bool(uint64_t n, bool b) {
  return (n + bool_to_nat(b));
}

uint64_t Coercions::double_wrapped(const Coercions::Wrapper &w) {
  return (w.unwrap + w.unwrap);
}

uint64_t Coercions::add_boolbox(uint64_t n, const Coercions::BoolBox &bb) {
  return (n + bool_to_nat(bb.unbox));
}
