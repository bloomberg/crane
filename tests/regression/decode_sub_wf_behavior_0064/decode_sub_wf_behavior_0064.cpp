#include <algorithm>
#include <any>
#include <cassert>
#include <decode_sub_wf_behavior_0064.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeSubWfBehavior0064::regs(
    const std::shared_ptr<DecodeSubWfBehavior0064::state> &s) {
  return s->regs;
}

bool DecodeSubWfBehavior0064::carry(
    const std::shared_ptr<DecodeSubWfBehavior0064::state> &s) {
  return s->carry;
}

unsigned int DecodeSubWfBehavior0064::pc(
    const std::shared_ptr<DecodeSubWfBehavior0064::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> DecodeSubWfBehavior0064::ram_sys(
    const std::shared_ptr<DecodeSubWfBehavior0064::state> &s) {
  return s->ram_sys;
}

std::shared_ptr<List<unsigned int>> DecodeSubWfBehavior0064::rom(
    const std::shared_ptr<DecodeSubWfBehavior0064::state> &s) {
  return s->rom;
}

std::shared_ptr<DecodeSubWfBehavior0064::state>
DecodeSubWfBehavior0064::reset_state(
    std::shared_ptr<DecodeSubWfBehavior0064::state> s) {
  return std::make_shared<DecodeSubWfBehavior0064::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
