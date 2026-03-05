#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reset_state_pc_clear.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>>
ResetStatePcClear::regs(const std::shared_ptr<ResetStatePcClear::state> &s) {
  return s->regs;
}

bool ResetStatePcClear::carry(
    const std::shared_ptr<ResetStatePcClear::state> &s) {
  return s->carry;
}

unsigned int
ResetStatePcClear::pc(const std::shared_ptr<ResetStatePcClear::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>>
ResetStatePcClear::ram_sys(const std::shared_ptr<ResetStatePcClear::state> &s) {
  return s->ram_sys;
}

std::shared_ptr<List<unsigned int>>
ResetStatePcClear::rom(const std::shared_ptr<ResetStatePcClear::state> &s) {
  return s->rom;
}

std::shared_ptr<ResetStatePcClear::state>
ResetStatePcClear::reset_state(std::shared_ptr<ResetStatePcClear::state> s) {
  return std::make_shared<ResetStatePcClear::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
