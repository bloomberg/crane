#include "sig_arg_match.h"

Nat SigArgMatch::addp(const Nat &p, const Nat &q) {
  // Precondition: q >= 1
  // Precondition: p >= 1
  return p.add(q);
}
