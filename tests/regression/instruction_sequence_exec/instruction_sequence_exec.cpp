#include "instruction_sequence_exec.h"

InstructionSequenceExec::state InstructionSequenceExec::execute(
    InstructionSequenceExec::state s,
    const InstructionSequenceExec::instruction &i) {
  if (std::holds_alternative<
          typename InstructionSequenceExec::instruction::NOP_>(i.v())) {
    return s;
  } else if (std::holds_alternative<
                 typename InstructionSequenceExec::instruction::INC_PC>(
                 i.v())) {
    return state{(s.pc_ + 1), s.acc_};
  } else {
    const auto &[a0] =
        std::get<typename InstructionSequenceExec::instruction::ADD_ACC>(i.v());
    return state{s.pc_, (s.acc_ + a0)};
  }
}

InstructionSequenceExec::state InstructionSequenceExec::exec_program(
    const List<InstructionSequenceExec::instruction> &prog,
    InstructionSequenceExec::state s) {
  if (std::holds_alternative<
          typename List<InstructionSequenceExec::instruction>::Nil>(prog.v())) {
    return s;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<InstructionSequenceExec::instruction>::Cons>(
            prog.v());
    return exec_program(*a1, execute(std::move(s), a0));
  }
}
