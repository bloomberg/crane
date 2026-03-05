#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <isz_terminates_at_max.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
IszTerminatesAtMax::regs(const std::shared_ptr<IszTerminatesAtMax::state> &s) {
  return s->regs;
}

unsigned int
IszTerminatesAtMax::get_reg(const std::shared_ptr<IszTerminatesAtMax::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int IszTerminatesAtMax::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

bool IszTerminatesAtMax::isz_terminates(
    const std::shared_ptr<IszTerminatesAtMax::state> &s, const unsigned int r) {
  return (nibble_of_nat((get_reg(s, r) + (0 + 1))) == 0);
}
