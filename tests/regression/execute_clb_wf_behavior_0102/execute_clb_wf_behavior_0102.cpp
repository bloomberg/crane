#include <algorithm>
#include <any>
#include <cassert>
#include <execute_clb_wf_behavior_0102.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> ExecuteClbWfBehavior0102::regs(
    const std::shared_ptr<ExecuteClbWfBehavior0102::state> &s) {
  return s->regs;
}

bool ExecuteClbWfBehavior0102::carry(
    const std::shared_ptr<ExecuteClbWfBehavior0102::state> &s) {
  return s->carry;
}

unsigned int ExecuteClbWfBehavior0102::pc(
    const std::shared_ptr<ExecuteClbWfBehavior0102::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> ExecuteClbWfBehavior0102::ram_sys(
    const std::shared_ptr<ExecuteClbWfBehavior0102::state> &s) {
  return s->ram_sys;
}

std::shared_ptr<List<unsigned int>> ExecuteClbWfBehavior0102::rom(
    const std::shared_ptr<ExecuteClbWfBehavior0102::state> &s) {
  return s->rom;
}

std::shared_ptr<ExecuteClbWfBehavior0102::state>
ExecuteClbWfBehavior0102::reset_state(
    std::shared_ptr<ExecuteClbWfBehavior0102::state> s) {
  return std::make_shared<ExecuteClbWfBehavior0102::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
