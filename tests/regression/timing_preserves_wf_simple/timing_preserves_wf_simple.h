#ifndef INCLUDED_TIMING_PRESERVES_WF_SIMPLE
#define INCLUDED_TIMING_PRESERVES_WF_SIMPLE

#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
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
