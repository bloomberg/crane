#ifndef INCLUDED_TIMING_PRESERVES_WF_SIMPLE
#define INCLUDED_TIMING_PRESERVES_WF_SIMPLE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

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
      return state{(*(this)).regs_len, (*(this)).rom_len, (*(this)).pc,
                   (*(this)).stack_len};
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
