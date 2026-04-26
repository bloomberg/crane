#ifndef INCLUDED_OPCODE_OPERAND_DECODE
#define INCLUDED_OPCODE_OPERAND_DECODE

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

struct OpcodeOperandDecode {
  enum class Instruction { e_NOP_, e_WRM_, e_WRR_, e_RDM_, e_DCL_ };

  template <typename T1>
  static T1 instruction_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const T1 f3, const Instruction i) {
    switch (i) {
    case Instruction::e_NOP_: {
      return f;
    }
    case Instruction::e_WRM_: {
      return f0;
    }
    case Instruction::e_WRR_: {
      return f1;
    }
    case Instruction::e_RDM_: {
      return f2;
    }
    case Instruction::e_DCL_: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 instruction_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const T1 f3, const Instruction i) {
    switch (i) {
    case Instruction::e_NOP_: {
      return f;
    }
    case Instruction::e_WRM_: {
      return f0;
    }
    case Instruction::e_WRR_: {
      return f1;
    }
    case Instruction::e_RDM_: {
      return f2;
    }
    case Instruction::e_DCL_: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static Instruction decode(const unsigned int &b1,
                                                  const unsigned int &_x);
  static inline const unsigned int t = []() {
    switch (decode(224u, 0u)) {
    case Instruction::e_WRM_: {
      return 1u;
    }
    default: {
      return 0u;
    }
    }
  }();
};

#endif // INCLUDED_OPCODE_OPERAND_DECODE
