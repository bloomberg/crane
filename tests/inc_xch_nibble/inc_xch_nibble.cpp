#include "inc_xch_nibble.h"

uint64_t IncXchNibble::get_reg(const IncXchNibble::state &s, uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

uint64_t IncXchNibble::nibble_of_nat(uint64_t n) {
  return (UINT64_C(16) ? n % UINT64_C(16) : n);
}

uint64_t IncXchNibble::get_reg_pair(const IncXchNibble::state &s, uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

IncXchNibble::state IncXchNibble::execute_inc(const IncXchNibble::state &s,
                                              uint64_t r) {
  return state{update_nth<uint64_t>(
                   r, nibble_of_nat((get_reg(s, r) + UINT64_C(1))), s.regs),
               s.acc};
}

IncXchNibble::state IncXchNibble::execute_xch(const IncXchNibble::state &s,
                                              uint64_t r) {
  return state{update_nth<uint64_t>(r, nibble_of_nat(s.acc), s.regs),
               get_reg(s, r)};
}
