#include <coercions.h>

unsigned int Coercions::bool_to_nat(const bool &b) {
  if (b) {
    return 1u;
  } else {
    return 0u;
  }
}

unsigned int Coercions::add_bool(const unsigned int &n, const bool &b) {
  return (n + bool_to_nat(b));
}

unsigned int Coercions::double_wrapped(const Coercions::Wrapper &w) {
  return (w.unwrap + w.unwrap);
}

unsigned int Coercions::add_boolbox(const unsigned int &n,
                                    const Coercions::BoolBox &bb) {
  return (n + bool_to_nat(bb.unbox));
}
