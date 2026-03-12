#include <timing_preserves_wf_simple.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

bool TimingPreservesWfSimple::wf(
    const std::shared_ptr<TimingPreservesWfSimple::state> &s) {
  return ((s->regs_len == 4u) &&
          ((s->rom_len == 4u) && ((s->pc < 4096u) && (s->stack_len <= 3u))));
}

unsigned int
TimingPreservesWfSimple::cycles(const TimingPreservesWfSimple::instr i) {
  return [&](void) {
    switch (i) {
    case instr::NOP: {
      return 8u;
    }
    case instr::ADD: {
      return 8u;
    }
    case instr::WRM: {
      return 8u;
    }
    case instr::FIM: {
      return 16u;
    }
    case instr::JMS: {
      return 24u;
    }
    }
  }();
}

std::shared_ptr<TimingPreservesWfSimple::state>
TimingPreservesWfSimple::execute(
    std::shared_ptr<TimingPreservesWfSimple::state> s,
    const TimingPreservesWfSimple::instr i) {
  return [&](void) {
    switch (i) {
    case instr::NOP: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, s->stack_len});
    }
    case instr::ADD: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, s->stack_len});
    }
    case instr::WRM: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, s->stack_len});
    }
    case instr::FIM: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, s->stack_len});
    }
    case instr::JMS: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, (s->stack_len + 1)});
    }
    }
  }();
}
