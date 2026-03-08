#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <isz_cycle_branch.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int
IszCycleBranch::get_reg(const std::shared_ptr<IszCycleBranch::state> &s,
                        const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int IszCycleBranch::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

unsigned int
IszCycleBranch::cycles_isz(const std::shared_ptr<IszCycleBranch::state> &s,
                           const unsigned int r) {
  unsigned int new_val = nibble_of_nat((get_reg(s, r) + 1u));
  if ((new_val == 0u)) {
    return 8u;
  } else {
    return 16u;
  }
}
