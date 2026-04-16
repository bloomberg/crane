#ifndef INCLUDED_TIMING_PRESERVES_WF_SIMPLE
#define INCLUDED_TIMING_PRESERVES_WF_SIMPLE

#include <memory>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct TimingPreservesWfSimple {
  enum class Instr { e_NOP, e_ADD, e_WRM, e_FIM, e_JMS };

  template <typename T1>
  static T1 instr_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const Instr i) {
    switch (i) {
    case Instr::e_NOP: {
      return f;
    }
    case Instr::e_ADD: {
      return f0;
    }
    case Instr::e_WRM: {
      return f1;
    }
    case Instr::e_FIM: {
      return f2;
    }
    case Instr::e_JMS: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 instr_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const Instr i) {
    switch (i) {
    case Instr::e_NOP: {
      return f;
    }
    case Instr::e_ADD: {
      return f0;
    }
    case Instr::e_WRM: {
      return f1;
    }
    case Instr::e_FIM: {
      return f2;
    }
    case Instr::e_JMS: {
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
  };

  __attribute__((pure)) static bool wf(const std::shared_ptr<state> &s);
  __attribute__((pure)) static unsigned int cycles(const Instr i);
  static std::shared_ptr<state> execute(const std::shared_ptr<state> &s,
                                        const Instr i);
  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{4u, 4u, 100u, 2u});
  static inline const bool t =
      (wf(sample) &&
       (cycles(Instr::e_JMS) == 24u && (wf(execute(sample, Instr::e_NOP)) &&
                                        wf(execute(sample, Instr::e_FIM)))));
};

#endif // INCLUDED_TIMING_PRESERVES_WF_SIMPLE
