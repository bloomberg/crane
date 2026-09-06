#include "sig_arg_match.h"

Nat SigArgMatch::addp(const Sig<Nat> &p,
                      const Sig<Nat> &q) { // Precondition: p >= 1
  assert(p >= 1);
  // Precondition: p >= 1
  assert(p >= 1);
  return [=]() mutable {
    const auto &[x] = p;
    return x;
  }()
             .add([=]() mutable {
               const auto &[x0] = q;
               return x0;
             }());
}
