#include "sig_parameter_le_precondition.h"

uint64_t SigParameterLePrecondition::get(
    uint64_t _x, const Sig<uint64_t> &b) { // Precondition: _x <= %1
  const auto &[x] = b;
  return x;
}

uint64_t SigParameterLePrecondition::get2(
    uint64_t _x, const Sig<uint64_t> &b) { // Precondition: (n <= m)
  return get(_x, b);
}
