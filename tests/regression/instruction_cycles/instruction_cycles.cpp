#include <instruction_cycles.h>

unsigned int
InstructionCycles::cycles_jms(const InstructionCycles::state2 &,
                              const InstructionCycles::instruction2 &i) {
  if (std::holds_alternative<typename InstructionCycles::instruction2::JMS2>(
          i.v())) {
    return 24u;
  } else {
    return 8u;
  }
}

unsigned int InstructionCycles::cycles_min(const InstructionCycles::Instr3 i) {
  switch (i) {
  case Instr3::e_FIM3: {
    return 16u;
  }
  case Instr3::e_JMS3: {
    return 24u;
  }
  case Instr3::e_JCNTAKEN3: {
    return 16u;
  }
  case Instr3::e_ISZTAKEN3: {
    return 16u;
  }
  default: {
    return 8u;
  }
  }
}

unsigned int InstructionCycles::cycles_max(const InstructionCycles::Instr4 i) {
  switch (i) {
  case Instr4::e_FIM4: {
    return 16u;
  }
  case Instr4::e_JMS4: {
    return 24u;
  }
  case Instr4::e_JCNTAKEN4: {
    return 16u;
  }
  case Instr4::e_ISZTAKEN4: {
    return 16u;
  }
  default: {
    return 8u;
  }
  }
}

unsigned int InstructionCycles::program_cycles5(
    const InstructionCycles::state5 &s,
    const List<InstructionCycles::instruction5> &prog) {
  if (std::holds_alternative<
          typename List<InstructionCycles::instruction5>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<InstructionCycles::instruction5>::Cons>(
            prog.v());
    return (d_a0.cycles_sum(s) + program_cycles5(d_a0.execute5(s), *(d_a1)));
  }
}

unsigned int InstructionCycles::cycles6(const InstructionCycles::state6 &,
                                        const InstructionCycles::Instruction6) {
  return 8u;
}

unsigned int InstructionCycles::program_cycles6(
    const InstructionCycles::state6 &s,
    const List<InstructionCycles::Instruction6> &prog) {
  if (std::holds_alternative<
          typename List<InstructionCycles::Instruction6>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<InstructionCycles::Instruction6>::Cons>(
            prog.v());
    return (cycles6(s, d_a0) + program_cycles6(s, *(d_a1)));
  }
}

unsigned int InstructionCycles::cycles7(const InstructionCycles::state7 &,
                                        const InstructionCycles::Instruction7) {
  return 8u;
}

unsigned int InstructionCycles::program_cycles7(
    const InstructionCycles::state7 &s,
    const List<InstructionCycles::Instruction7> &prog) {
  if (std::holds_alternative<
          typename List<InstructionCycles::Instruction7>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<InstructionCycles::Instruction7>::Cons>(
            prog.v());
    return (cycles7(s, d_a0) + program_cycles7(s, *(d_a1)));
  }
}
