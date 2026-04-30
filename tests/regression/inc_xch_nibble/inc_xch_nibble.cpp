#include <inc_xch_nibble.h>

unsigned int IncXchNibble::get_reg(const IncXchNibble::state &s,
                                   const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.regs, 0u);
}

unsigned int IncXchNibble::nibble_of_nat(const unsigned int &n) {
  return (16u ? n % 16u : n);
}

unsigned int IncXchNibble::get_reg_pair(const IncXchNibble::state &s,
                                        const unsigned int &r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

IncXchNibble::state IncXchNibble::execute_inc(const IncXchNibble::state &s,
                                              const unsigned int &r) {
  return state{
      update_nth<unsigned int>(r, nibble_of_nat((get_reg(s, r) + 1u)), s.regs),
      s.acc};
}

IncXchNibble::state IncXchNibble::execute_xch(const IncXchNibble::state &s,
                                              const unsigned int &r) {
  return state{update_nth<unsigned int>(r, nibble_of_nat(s.acc), s.regs),
               get_reg(s, r)};
}
