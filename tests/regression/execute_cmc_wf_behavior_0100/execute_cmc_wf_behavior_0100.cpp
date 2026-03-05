#include <algorithm>
#include <any>
#include <cassert>
#include <execute_cmc_wf_behavior_0100.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> ExecuteCmcWfBehavior0100::regs(
    const std::shared_ptr<ExecuteCmcWfBehavior0100::state> &s) {
  return s->regs;
}

bool ExecuteCmcWfBehavior0100::carry(
    const std::shared_ptr<ExecuteCmcWfBehavior0100::state> &s) {
  return s->carry;
}

unsigned int ExecuteCmcWfBehavior0100::pc(
    const std::shared_ptr<ExecuteCmcWfBehavior0100::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> ExecuteCmcWfBehavior0100::ram_sys(
    const std::shared_ptr<ExecuteCmcWfBehavior0100::state> &s) {
  return s->ram_sys;
}

std::shared_ptr<List<unsigned int>> ExecuteCmcWfBehavior0100::rom(
    const std::shared_ptr<ExecuteCmcWfBehavior0100::state> &s) {
  return s->rom;
}

std::shared_ptr<ExecuteCmcWfBehavior0100::state>
ExecuteCmcWfBehavior0100::reset_state(
    std::shared_ptr<ExecuteCmcWfBehavior0100::state> s) {
  return std::make_shared<ExecuteCmcWfBehavior0100::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
