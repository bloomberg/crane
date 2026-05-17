#include "instruction_classifiers.h"

unsigned int InstructionClassifiers::count_writes_acc(
    const List<InstructionClassifiers::instr_acc> &prog) {
  if (std::holds_alternative<
          typename List<InstructionClassifiers::instr_acc>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<InstructionClassifiers::instr_acc>::Cons>(
            prog.v());
    return ((a0.writes_acc() ? 1u : 0u) + count_writes_acc(*a1));
  }
}

unsigned int InstructionClassifiers::count_writes_ram(
    const List<InstructionClassifiers::instr_ram> &prog) {
  if (std::holds_alternative<
          typename List<InstructionClassifiers::instr_ram>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<InstructionClassifiers::instr_ram>::Cons>(
            prog.v());
    return ((a0.writes_ram() ? 1u : 0u) + count_writes_ram(*a1));
  }
}

unsigned int InstructionClassifiers::count_writes_regs(
    const List<InstructionClassifiers::instr_regs> &prog) {
  if (std::holds_alternative<
          typename List<InstructionClassifiers::instr_regs>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<InstructionClassifiers::instr_regs>::Cons>(
            prog.v());
    return ((a0.writes_regs() ? 1u : 0u) + count_writes_regs(*a1));
  }
}

unsigned int InstructionClassifiers::count_jumps(
    const List<InstructionClassifiers::instr_jump> &prog) {
  if (std::holds_alternative<
          typename List<InstructionClassifiers::instr_jump>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<InstructionClassifiers::instr_jump>::Cons>(
            prog.v());
    return ((a0.is_jump() ? 1u : 0u) + count_jumps(*a1));
  }
}
