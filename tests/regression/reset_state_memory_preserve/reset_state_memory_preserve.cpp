#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reset_state_memory_preserve.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ResetStateMemoryPreserve::acc(
    const std::shared_ptr<ResetStateMemoryPreserve::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>> ResetStateMemoryPreserve::regs(
    const std::shared_ptr<ResetStateMemoryPreserve::state> &s) {
  return s->regs;
}

bool ResetStateMemoryPreserve::carry(
    const std::shared_ptr<ResetStateMemoryPreserve::state> &s) {
  return s->carry;
}

unsigned int ResetStateMemoryPreserve::pc(
    const std::shared_ptr<ResetStateMemoryPreserve::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> ResetStateMemoryPreserve::stack(
    const std::shared_ptr<ResetStateMemoryPreserve::state> &s) {
  return s->stack;
}

std::shared_ptr<List<unsigned int>> ResetStateMemoryPreserve::ram_sys(
    const std::shared_ptr<ResetStateMemoryPreserve::state> &s) {
  return s->ram_sys;
}

std::shared_ptr<List<unsigned int>> ResetStateMemoryPreserve::rom(
    const std::shared_ptr<ResetStateMemoryPreserve::state> &s) {
  return s->rom;
}

std::shared_ptr<ResetStateMemoryPreserve::state>
ResetStateMemoryPreserve::reset_state(
    std::shared_ptr<ResetStateMemoryPreserve::state> s) {
  return std::make_shared<ResetStateMemoryPreserve::state>(
      state{0, s->regs, false, 0, List<unsigned int>::ctor::nil_(), s->ram_sys,
            s->rom});
}
