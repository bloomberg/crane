#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reg_pair_successor.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int
RegPairSuccessor::get_reg(const std::shared_ptr<RegPairSuccessor::state> &s,
                          const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int RegPairSuccessor::get_reg_pair(
    const std::shared_ptr<RegPairSuccessor::state> &s, const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}
