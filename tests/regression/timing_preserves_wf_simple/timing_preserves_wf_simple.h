#ifndef INCLUDED_TIMING_PRESERVES_WF_SIMPLE
#define INCLUDED_TIMING_PRESERVES_WF_SIMPLE

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

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct TimingPreservesWfSimple {
  enum class instr { NOP, ADD, WRM, FIM, JMS };

  template <typename T1>
  static T1 instr_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const instr i) {
    return [&](void) {
      switch (i) {
      case instr::NOP: {
        return f;
      }
      case instr::ADD: {
        return f0;
      }
      case instr::WRM: {
        return f1;
      }
      case instr::FIM: {
        return f2;
      }
      case instr::JMS: {
        return f3;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instr_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const instr i) {
    return [&](void) {
      switch (i) {
      case instr::NOP: {
        return f;
      }
      case instr::ADD: {
        return f0;
      }
      case instr::WRM: {
        return f1;
      }
      case instr::FIM: {
        return f2;
      }
      case instr::JMS: {
        return f3;
      }
      }
    }();
  }

  struct state {
    unsigned int regs_len;
    unsigned int rom_len;
    unsigned int pc;
    unsigned int stack_len;
  };

  static bool wf(const std::shared_ptr<state> &s);
  static unsigned int cycles(const instr i);
  static std::shared_ptr<state> execute(std::shared_ptr<state> s,
                                        const instr i);
  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{4u, 4u, 100u, 2u});
  static inline const bool t =
      (wf(sample) &&
       ((cycles(instr::JMS) == 24u) &&
        (wf(execute(sample, instr::NOP)) && wf(execute(sample, instr::FIM)))));
};

#endif // INCLUDED_TIMING_PRESERVES_WF_SIMPLE
