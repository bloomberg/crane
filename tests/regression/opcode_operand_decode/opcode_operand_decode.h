#ifndef INCLUDED_OPCODE_OPERAND_DECODE
#define INCLUDED_OPCODE_OPERAND_DECODE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

struct OpcodeOperandDecode {
  enum class Instruction { e_NOP_, e_WRM_, e_WRR_, e_RDM_, e_DCL_ };

  template <typename T1>
  static T1 instruction_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3,
                             const Instruction i) {
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
  static T1 instruction_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3,
                            const Instruction i) {
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

  static Instruction decode(const unsigned int b1, const unsigned int _x);
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
