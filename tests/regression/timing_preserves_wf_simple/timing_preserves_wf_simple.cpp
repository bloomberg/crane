#include <timing_preserves_wf_simple.h>

bool TimingPreservesWfSimple::wf(const TimingPreservesWfSimple::state &s) {
  return (s.regs_len == 4u &&
          (s.rom_len == 4u && (s.pc < 4096u && s.stack_len <= 3u)));
}

unsigned int
TimingPreservesWfSimple::cycles(const TimingPreservesWfSimple::Instr i) {
  switch (i) {
  case Instr::e_FIM: {
    return 16u;
  }
  case Instr::e_JMS: {
    return 24u;
  }
  default: {
    return 8u;
  }
  }
}

TimingPreservesWfSimple::state
TimingPreservesWfSimple::execute(const TimingPreservesWfSimple::state &s,
                                 const TimingPreservesWfSimple::Instr i) {
  switch (i) {
  case Instr::e_JMS: {
    return state{s.regs_len, s.rom_len, s.pc, (s.stack_len + 1)};
  }
  default: {
    return state{s.regs_len, s.rom_len, s.pc, s.stack_len};
  }
  }
}
