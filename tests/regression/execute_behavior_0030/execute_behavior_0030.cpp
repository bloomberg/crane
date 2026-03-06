#include <algorithm>
#include <any>
#include <cassert>
#include <execute_behavior_0030.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> ExecuteBehavior0030::regs(
    const std::shared_ptr<ExecuteBehavior0030::state> &s) {
  return s->regs;
}

bool ExecuteBehavior0030::carry(
    const std::shared_ptr<ExecuteBehavior0030::state> &s) {
  return s->carry;
}

unsigned int
ExecuteBehavior0030::pc(const std::shared_ptr<ExecuteBehavior0030::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> ExecuteBehavior0030::ram_sys(
    const std::shared_ptr<ExecuteBehavior0030::state> &s) {
  return s->ram_sys;
}

std::shared_ptr<List<unsigned int>>
ExecuteBehavior0030::rom(const std::shared_ptr<ExecuteBehavior0030::state> &s) {
  return s->rom;
}

std::shared_ptr<ExecuteBehavior0030::state> ExecuteBehavior0030::reset_state(
    std::shared_ptr<ExecuteBehavior0030::state> s) {
  return std::make_shared<ExecuteBehavior0030::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
