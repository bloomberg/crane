#include "instruction_cycles.h"

uint64_t
InstructionCycles::cycles_jms(const InstructionCycles::state2 &,
                              const InstructionCycles::instruction2 &i) {
  if (std::holds_alternative<typename InstructionCycles::instruction2::JMS2>(
          i.v())) {
    return UINT64_C(24);
  } else {
    return UINT64_C(8);
  }
}

uint64_t InstructionCycles::cycles_min(InstructionCycles::Instr3 i) {
  switch (i) {
  case Instr3::FIM3: {
    return UINT64_C(16);
  }
  case Instr3::JMS3: {
    return UINT64_C(24);
  }
  case Instr3::JCNTAKEN3: {
    return UINT64_C(16);
  }
  case Instr3::ISZTAKEN3: {
    return UINT64_C(16);
  }
  default: {
    return UINT64_C(8);
  }
  }
}

uint64_t InstructionCycles::cycles_max(InstructionCycles::Instr4 i) {
  switch (i) {
  case Instr4::FIM4: {
    return UINT64_C(16);
  }
  case Instr4::JMS4: {
    return UINT64_C(24);
  }
  case Instr4::JCNTAKEN4: {
    return UINT64_C(16);
  }
  case Instr4::ISZTAKEN4: {
    return UINT64_C(16);
  }
  default: {
    return UINT64_C(8);
  }
  }
}

uint64_t InstructionCycles::program_cycles5(
    const InstructionCycles::state5 &s,
    const List<InstructionCycles::instruction5> &prog) {
  if (std::holds_alternative<
          typename List<InstructionCycles::instruction5>::Nil>(prog.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<InstructionCycles::instruction5>::Cons>(
            prog.v());
    return (a0.cycles_sum(s) + program_cycles5(a0.execute5(s), *a1));
  }
}

uint64_t InstructionCycles::cycles6(const InstructionCycles::state6 &,
                                    InstructionCycles::Instruction6) {
  return UINT64_C(8);
}

uint64_t InstructionCycles::program_cycles6(
    const InstructionCycles::state6 &s,
    const List<InstructionCycles::Instruction6> &prog) {
  if (std::holds_alternative<
          typename List<InstructionCycles::Instruction6>::Nil>(prog.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<InstructionCycles::Instruction6>::Cons>(
            prog.v());
    return (cycles6(s, a0) + program_cycles6(s, *a1));
  }
}

uint64_t InstructionCycles::cycles7(const InstructionCycles::state7 &,
                                    InstructionCycles::Instruction7) {
  return UINT64_C(8);
}

uint64_t InstructionCycles::program_cycles7(
    const InstructionCycles::state7 &s,
    const List<InstructionCycles::Instruction7> &prog) {
  if (std::holds_alternative<
          typename List<InstructionCycles::Instruction7>::Nil>(prog.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<InstructionCycles::Instruction7>::Cons>(
            prog.v());
    return (cycles7(s, a0) + program_cycles7(s, *a1));
  }
}
