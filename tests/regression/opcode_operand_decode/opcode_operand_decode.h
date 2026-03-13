#ifndef INCLUDED_OPCODE_OPERAND_DECODE
#define INCLUDED_OPCODE_OPERAND_DECODE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct OpcodeOperandDecode {
  enum class Instruction { e_NOP_, e_WRM_, e_WRR_, e_RDM_, e_DCL_ };

  template <typename T1>
  static T1 instruction_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const T1 f3, const Instruction i) {
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 instruction_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const T1 f3, const Instruction i) {
    return [&](void) {
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
      }
    }();
  }

  __attribute__((pure)) static Instruction decode(const unsigned int b1,
                                                  const unsigned int _x);
  static inline const unsigned int t = [](void) {
    switch (decode(224u, 0u)) {
    case Instruction::e_NOP_: {
      return 0u;
    }
    case Instruction::e_WRM_: {
      return 1u;
    }
    case Instruction::e_WRR_: {
      return 0u;
    }
    case Instruction::e_RDM_: {
      return 0u;
    }
    case Instruction::e_DCL_: {
      return 0u;
    }
    }
  }();
};

#endif // INCLUDED_OPCODE_OPERAND_DECODE
