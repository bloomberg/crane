#ifndef INCLUDED_OPCODE_OPERAND_DECODE
#define INCLUDED_OPCODE_OPERAND_DECODE

#include <utility>

struct OpcodeOperandDecode {
  enum class Instruction { NOP_, WRM_, WRR_, RDM_, DCL_ };

  template <typename T1>
  static T1 instruction_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, Instruction i) {
    switch (i) {
    case Instruction::NOP_: {
      return f;
    }
    case Instruction::WRM_: {
      return f0;
    }
    case Instruction::WRR_: {
      return f1;
    }
    case Instruction::RDM_: {
      return f2;
    }
    case Instruction::DCL_: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 instruction_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, Instruction i) {
    switch (i) {
    case Instruction::NOP_: {
      return f;
    }
    case Instruction::WRM_: {
      return f0;
    }
    case Instruction::WRR_: {
      return f1;
    }
    case Instruction::RDM_: {
      return f2;
    }
    case Instruction::DCL_: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  static Instruction decode(uint64_t b1, uint64_t _x);
  static inline const uint64_t t = []() {
    switch (decode(UINT64_C(224), UINT64_C(0))) {
    case Instruction::WRM_: {
      return UINT64_C(1);
    }
    default: {
      return UINT64_C(0);
    }
    }
  }();
};

#endif // INCLUDED_OPCODE_OPERAND_DECODE
