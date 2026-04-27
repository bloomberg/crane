#ifndef INCLUDED_TIMING_PRESERVES_WF_SIMPLE
#define INCLUDED_TIMING_PRESERVES_WF_SIMPLE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).regs_len),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).rom_len),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).pc),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).stack_len)};
    }
  };

  __attribute__((pure)) static bool wf(const state &s);
  __attribute__((pure)) static unsigned int cycles(const Instr i);
  __attribute__((pure)) static state execute(const state &s, const Instr i);
  static inline const state sample = state{4u, 4u, 100u, 2u};
  static inline const bool t =
      (wf(sample) &&
       (cycles(Instr::e_JMS) == 24u && (wf(execute(sample, Instr::e_NOP)) &&
                                        wf(execute(sample, Instr::e_FIM)))));
};

#endif // INCLUDED_TIMING_PRESERVES_WF_SIMPLE
