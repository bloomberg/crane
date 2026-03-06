#include <algorithm>
#include <any>
#include <cassert>
#include <encode_behavior_0020.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
EncodeBehavior0020::regs(const std::shared_ptr<EncodeBehavior0020::state> &s) {
  return s->regs;
}

unsigned int
EncodeBehavior0020::get_reg(const std::shared_ptr<EncodeBehavior0020::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int EncodeBehavior0020::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

bool EncodeBehavior0020::isz_loops(
    const std::shared_ptr<EncodeBehavior0020::state> &s, const unsigned int r) {
  return !((nibble_of_nat((get_reg(s, r) + (0 + 1))) == 0));
}
