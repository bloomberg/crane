#ifndef INCLUDED_TIMING_PRESERVES_WF_SIMPLE
#define INCLUDED_TIMING_PRESERVES_WF_SIMPLE

#include <utility>

struct TimingPreservesWfSimple {
  enum class Instr { NOP, ADD, WRM, FIM, JMS };

  template <typename T1>
  static T1 instr_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, Instr i) {
    switch (i) {
    case Instr::NOP: {
      return f;
    }
    case Instr::ADD: {
      return f0;
    }
    case Instr::WRM: {
      return f1;
    }
    case Instr::FIM: {
      return f2;
    }
    case Instr::JMS: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 instr_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, Instr i) {
    switch (i) {
    case Instr::NOP: {
      return f;
    }
    case Instr::ADD: {
      return f0;
    }
    case Instr::WRM: {
      return f1;
    }
    case Instr::FIM: {
      return f2;
    }
    case Instr::JMS: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  struct state {
    uint64_t regs_len;
    uint64_t rom_len;
    uint64_t pc;
    uint64_t stack_len;

    // ACCESSORS
    state clone() const {
      return state{this->regs_len, this->rom_len, this->pc, this->stack_len};
    }
  };

  static bool wf(const state &s);
  static uint64_t cycles(Instr i);
  static state execute(const state &s, Instr i);
  static inline const state sample =
      state{UINT64_C(4), UINT64_C(4), UINT64_C(100), UINT64_C(2)};
  static inline const bool t =
      (wf(sample) &&
       (cycles(Instr::JMS) == UINT64_C(24) &&
        (wf(execute(sample, Instr::NOP)) && wf(execute(sample, Instr::FIM)))));
};

#endif // INCLUDED_TIMING_PRESERVES_WF_SIMPLE
