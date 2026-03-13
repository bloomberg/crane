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

__attribute__((pure)) bool TimingPreservesWfSimple::wf(
    const std::shared_ptr<TimingPreservesWfSimple::state> &s) {
  return (s->regs_len == 4u &&
          (s->rom_len == 4u && (s->pc < 4096u && s->stack_len <= 3u)));
}

__attribute__((pure)) unsigned int
TimingPreservesWfSimple::cycles(const TimingPreservesWfSimple::Instr i) {
  return [&](void) {
    switch (i) {
    case Instr::e_NOP: {
      return 8u;
    }
    case Instr::e_ADD: {
      return 8u;
    }
    case Instr::e_WRM: {
      return 8u;
    }
    case Instr::e_FIM: {
      return 16u;
    }
    case Instr::e_JMS: {
      return 24u;
    }
    }
  }();
}

std::shared_ptr<TimingPreservesWfSimple::state>
TimingPreservesWfSimple::execute(
    std::shared_ptr<TimingPreservesWfSimple::state> s,
    const TimingPreservesWfSimple::Instr i) {
  return [&](void) {
    switch (i) {
    case Instr::e_NOP: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, s->stack_len});
    }
    case Instr::e_ADD: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, s->stack_len});
    }
    case Instr::e_WRM: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, s->stack_len});
    }
    case Instr::e_FIM: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, s->stack_len});
    }
    case Instr::e_JMS: {
      return std::make_shared<TimingPreservesWfSimple::state>(
          state{s->regs_len, s->rom_len, s->pc, (s->stack_len + 1)});
    }
    }
  }();
}
