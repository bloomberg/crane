#include "timing_preserves_wf_simple.h"

bool TimingPreservesWfSimple::wf(const TimingPreservesWfSimple::state &s) {
  return (s.regs_len == UINT64_C(4) &&
          (s.rom_len == UINT64_C(4) &&
           (s.pc < UINT64_C(4096) && s.stack_len <= UINT64_C(3))));
}

uint64_t TimingPreservesWfSimple::cycles(TimingPreservesWfSimple::Instr i) {
  switch (i) {
  case Instr::FIM: {
    return UINT64_C(16);
  } break;
  case Instr::JMS: {
    return UINT64_C(24);
  } break;
  default: {
    return UINT64_C(8);
  }
  }
}

TimingPreservesWfSimple::state
TimingPreservesWfSimple::execute(const TimingPreservesWfSimple::state &s,
                                 TimingPreservesWfSimple::Instr i) {
  switch (i) {
  case Instr::JMS: {
    return state{s.regs_len, s.rom_len, s.pc, (s.stack_len + 1)};
  } break;
  default: {
    return state{s.regs_len, s.rom_len, s.pc, s.stack_len};
  }
  }
}
