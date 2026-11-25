#include "sig_parameter_le_precondition.h"

uint64_t SigParameterLePrecondition::get(uint64_t _x, uint64_t x0_) {
  // Precondition: x0_ <= _x
  assert(x0_ <= _x);
  return x0_;
}

uint64_t SigParameterLePrecondition::get2(uint64_t _x, uint64_t x0_) {
  // Precondition: _x <= x0_
  assert(_x <= x0_);
  return x0_;
}
