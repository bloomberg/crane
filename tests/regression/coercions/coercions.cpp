#include "coercions.h"

unsigned int Coercions::bool_to_nat(bool b) {
  if (b) {
    return 1u;
  } else {
    return 0u;
  }
}

unsigned int Coercions::add_bool(unsigned int n, bool b) {
  return (n + bool_to_nat(b));
}

unsigned int Coercions::double_wrapped(const Coercions::Wrapper &w) {
  return (w.unwrap + w.unwrap);
}

unsigned int Coercions::add_boolbox(unsigned int n,
                                    const Coercions::BoolBox &bb) {
  return (n + bool_to_nat(bb.unbox));
}
