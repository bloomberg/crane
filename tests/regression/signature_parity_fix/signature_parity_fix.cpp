#include "signature_parity_fix.h"

uint64_t SignatureParityFix::f(uint64_t seed) {
  auto aux_impl = [&](auto &_self_aux, uint64_t n) -> uint64_t {
    if (n <= 0) {
      return seed;
    } else {
      uint64_t n_ = n - 1;
      return _self_aux(_self_aux, n_);
    }
  };
  auto aux = [&](uint64_t n) -> uint64_t { return aux_impl(aux_impl, n); };
  return aux((seed + 1));
}
