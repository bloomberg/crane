#include <inc_xch_nibble.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
IncXchNibble::get_reg(const std::shared_ptr<IncXchNibble::state> &s,
                      const unsigned int r) {
  return s->regs->nth(r, 0u);
}

__attribute__((pure)) unsigned int
IncXchNibble::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

__attribute__((pure)) unsigned int
IncXchNibble::get_reg_pair(const std::shared_ptr<IncXchNibble::state> &s,
                           const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<IncXchNibble::state>
IncXchNibble::execute_inc(std::shared_ptr<IncXchNibble::state> s,
                          const unsigned int r) {
  return std::make_shared<IncXchNibble::state>(state{
      update_nth<unsigned int>(r, nibble_of_nat((get_reg(s, r) + 1u)), s->regs),
      s->acc});
}

std::shared_ptr<IncXchNibble::state>
IncXchNibble::execute_xch(std::shared_ptr<IncXchNibble::state> s,
                          const unsigned int r) {
  return std::make_shared<IncXchNibble::state>(
      state{update_nth<unsigned int>(r, nibble_of_nat(s->acc), s->regs),
            get_reg(s, r)});
}
