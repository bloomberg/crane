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

std::shared_ptr<List<unsigned int>>
IszCycleBranch::regs(const std::shared_ptr<IszCycleBranch::state> &s) {
  return s->regs;
}

unsigned int
IszCycleBranch::get_reg(const std::shared_ptr<IszCycleBranch::state> &s,
                        const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int IszCycleBranch::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

unsigned int
IszCycleBranch::cycles_isz(const std::shared_ptr<IszCycleBranch::state> &s,
                           const unsigned int r) {
  unsigned int new_val = nibble_of_nat((get_reg(s, r) + (0 + 1)));
  if ((new_val == 0)) {
    return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
  } else {
    return ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1);
  }
}
