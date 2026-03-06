#include <algorithm>
#include <any>
#include <cassert>
#include <decode_jin_wf_behavior_0058.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeJinWfBehavior0058::regs(
    const std::shared_ptr<DecodeJinWfBehavior0058::state> &s) {
  return s->regs;
}

unsigned int DecodeJinWfBehavior0058::get_reg(
    const std::shared_ptr<DecodeJinWfBehavior0058::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int DecodeJinWfBehavior0058::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

bool DecodeJinWfBehavior0058::isz_terminates(
    const std::shared_ptr<DecodeJinWfBehavior0058::state> &s,
    const unsigned int r) {
  return (nibble_of_nat((get_reg(s, r) + (0 + 1))) == 0);
}
