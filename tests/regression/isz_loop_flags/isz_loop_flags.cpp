#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <isz_loop_flags.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int IszLoopFlags::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

unsigned int
IszLoopFlags::get_reg(const std::shared_ptr<IszLoopFlags::state> &s,
                      const unsigned int r) {
  return s->regs->nth(r, 0u);
}

bool IszLoopFlags::isz_loops(const std::shared_ptr<IszLoopFlags::state> &s,
                             const unsigned int r) {
  return !((nibble_of_nat((get_reg(s, r) + 1u)) == 0u));
}

bool IszLoopFlags::isz_terminates(const std::shared_ptr<IszLoopFlags::state> &s,
                                  const unsigned int r) {
  return (nibble_of_nat((get_reg(s, r) + 1u)) == 0u);
}
