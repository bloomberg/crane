#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <get_reg_pair_odd_normalizes.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> GetRegPairOddNormalizes::regs(
    const std::shared_ptr<GetRegPairOddNormalizes::state> &s) {
  return s->regs;
}

unsigned int GetRegPairOddNormalizes::get_reg(
    const std::shared_ptr<GetRegPairOddNormalizes::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int GetRegPairOddNormalizes::get_reg_pair(
    const std::shared_ptr<GetRegPairOddNormalizes::state> &s,
    const unsigned int r) {
  unsigned int base =
      (((r - (r % ((0 + 1) + 1))) > r ? 0 : (r - (r % ((0 + 1) + 1)))));
  return ((get_reg(s, base) *
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)) +
          get_reg(s, (base + (0 + 1))));
}
