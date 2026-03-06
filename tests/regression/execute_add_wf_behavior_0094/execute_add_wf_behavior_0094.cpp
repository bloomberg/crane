#include <algorithm>
#include <any>
#include <cassert>
#include <execute_add_wf_behavior_0094.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> ExecuteAddWfBehavior0094::regs(
    const std::shared_ptr<ExecuteAddWfBehavior0094::state> &s) {
  return s->regs;
}

unsigned int ExecuteAddWfBehavior0094::get_reg(
    const std::shared_ptr<ExecuteAddWfBehavior0094::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int ExecuteAddWfBehavior0094::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

bool ExecuteAddWfBehavior0094::isz_terminates(
    const std::shared_ptr<ExecuteAddWfBehavior0094::state> &s,
    const unsigned int r) {
  return (nibble_of_nat((get_reg(s, r) + (0 + 1))) == 0);
}
