#include <timing_preserves_wf_simple.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

__attribute__((pure)) bool
TimingPreservesWfSimple::wf(const TimingPreservesWfSimple::state &s) {
  return (s.regs_len == 4u &&
          (s.rom_len == 4u && (s.pc < 4096u && s.stack_len <= 3u)));
}

__attribute__((pure)) unsigned int
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

__attribute__((pure)) TimingPreservesWfSimple::state
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
