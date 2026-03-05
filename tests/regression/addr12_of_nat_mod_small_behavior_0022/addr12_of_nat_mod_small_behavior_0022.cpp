#include <addr12_of_nat_mod_small_behavior_0022.h>
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

std::shared_ptr<List<unsigned int>> Addr12OfNatModSmallBehavior0022::regs(
    const std::shared_ptr<Addr12OfNatModSmallBehavior0022::state> &s) {
  return s->regs;
}

unsigned int Addr12OfNatModSmallBehavior0022::get_reg(
    const std::shared_ptr<Addr12OfNatModSmallBehavior0022::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int
Addr12OfNatModSmallBehavior0022::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

bool Addr12OfNatModSmallBehavior0022::isz_terminates(
    const std::shared_ptr<Addr12OfNatModSmallBehavior0022::state> &s,
    const unsigned int r) {
  return (nibble_of_nat((get_reg(s, r) + (0 + 1))) == 0);
}
