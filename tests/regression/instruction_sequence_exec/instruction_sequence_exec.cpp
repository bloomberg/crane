#include <instruction_sequence_exec.h>

__attribute__((pure)) InstructionSequenceExec::state
InstructionSequenceExec::execute(
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
    const auto &[d_a0] =
        std::get<typename InstructionSequenceExec::instruction::ADD_ACC>(i.v());
    return state{s.pc_, (s.acc_ + d_a0)};
  }
}

__attribute__((pure)) InstructionSequenceExec::state
InstructionSequenceExec::exec_program(
    const List<InstructionSequenceExec::instruction> &prog,
    InstructionSequenceExec::state s) {
  if (std::holds_alternative<
          typename List<InstructionSequenceExec::instruction>::Nil>(prog.v())) {
    return s;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<InstructionSequenceExec::instruction>::Cons>(
            prog.v());
    return exec_program(*(d_a1), execute(s, d_a0));
  }
}
