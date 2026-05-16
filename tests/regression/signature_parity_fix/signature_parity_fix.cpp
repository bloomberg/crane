#include "signature_parity_fix.h"

unsigned int SignatureParityFix::f(const unsigned int seed) {
  auto aux_impl = [&](auto &_self_aux, unsigned int n) -> unsigned int {
    if (n <= 0) {
      return seed;
    } else {
      unsigned int n_ = n - 1;
      return _self_aux(_self_aux, n_);
    }
  };
  auto aux = [&](unsigned int n) -> unsigned int {
    return aux_impl(aux_impl, n);
  };
  return aux((seed + 1));
}
