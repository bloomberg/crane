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
    unsigned int regs_len;
    unsigned int rom_len;
    unsigned int pc;
    unsigned int stack_len;

    // ACCESSORS
    state clone() const {
      return state{(*this).regs_len, (*this).rom_len, (*this).pc,
                   (*this).stack_len};
    }
  };

  static bool wf(const state &s);
  static unsigned int cycles(Instr i);
  static state execute(const state &s, Instr i);
  static inline const state sample = state{4u, 4u, 100u, 2u};
  static inline const bool t =
      (wf(sample) &&
       (cycles(Instr::JMS) == 24u &&
        (wf(execute(sample, Instr::NOP)) && wf(execute(sample, Instr::FIM)))));
};

#endif // INCLUDED_TIMING_PRESERVES_WF_SIMPLE
