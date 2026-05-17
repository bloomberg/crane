#include "isz_ops.h"

uint64_t IszOps::nibble_of_nat(uint64_t n) {
  return (UINT64_C(16) ? n % UINT64_C(16) : n);
}

uint64_t IszOps::get_reg(const IszOps::state &s, uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

uint64_t IszOps::cycles_isz(const IszOps::state &s, uint64_t r) {
  uint64_t new_val = nibble_of_nat((get_reg(s, r) + UINT64_C(1)));
  if (new_val == UINT64_C(0)) {
    return UINT64_C(8);
  } else {
    return UINT64_C(16);
  }
}

uint64_t IszOps::isz_iterations(uint64_t v) {
  if (v == UINT64_C(0)) {
    return UINT64_C(16);
  } else {
    return (((UINT64_C(16) - v) > UINT64_C(16) ? 0 : (UINT64_C(16) - v)));
  }
}

bool IszOps::isz_loops(const IszOps::state &s, uint64_t r) {
  return !(nibble_of_nat((get_reg(s, r) + UINT64_C(1))) == UINT64_C(0));
}

bool IszOps::isz_terminates(const IszOps::state &s, uint64_t r) {
  return nibble_of_nat((get_reg(s, r) + UINT64_C(1))) == UINT64_C(0);
}
