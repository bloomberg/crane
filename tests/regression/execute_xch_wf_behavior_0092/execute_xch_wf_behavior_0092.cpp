#include <algorithm>
#include <any>
#include <cassert>
#include <execute_xch_wf_behavior_0092.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> ExecuteXchWfBehavior0092::regs(
    const std::shared_ptr<ExecuteXchWfBehavior0092::state> &s) {
  return s->regs;
}

unsigned int ExecuteXchWfBehavior0092::get_reg(
    const std::shared_ptr<ExecuteXchWfBehavior0092::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int ExecuteXchWfBehavior0092::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

bool ExecuteXchWfBehavior0092::isz_loops(
    const std::shared_ptr<ExecuteXchWfBehavior0092::state> &s,
    const unsigned int r) {
  return !((nibble_of_nat((get_reg(s, r) + (0 + 1))) == 0));
}
