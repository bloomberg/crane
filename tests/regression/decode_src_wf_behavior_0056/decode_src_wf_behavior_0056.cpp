#include <algorithm>
#include <any>
#include <cassert>
#include <decode_src_wf_behavior_0056.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeSrcWfBehavior0056::regs(
    const std::shared_ptr<DecodeSrcWfBehavior0056::state> &s) {
  return s->regs;
}

unsigned int DecodeSrcWfBehavior0056::get_reg(
    const std::shared_ptr<DecodeSrcWfBehavior0056::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int DecodeSrcWfBehavior0056::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

bool DecodeSrcWfBehavior0056::isz_loops(
    const std::shared_ptr<DecodeSrcWfBehavior0056::state> &s,
    const unsigned int r) {
  return !((nibble_of_nat((get_reg(s, r) + (0 + 1))) == 0));
}
