#include <instruction_sequence_exec.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<InstructionSequenceExec::state>
InstructionSequenceExec::execute(
    std::shared_ptr<InstructionSequenceExec::state> s,
    const std::shared_ptr<InstructionSequenceExec::instruction> &i) {
  if (std::holds_alternative<
          typename InstructionSequenceExec::instruction::NOP_>(i->v())) {
    return s;
  } else if (std::holds_alternative<
                 typename InstructionSequenceExec::instruction::INC_PC>(
                 i->v())) {
    return std::make_shared<InstructionSequenceExec::state>(
        state{(s->pc_ + 1), s->acc_});
  } else {
    const auto &_m =
        *std::get_if<typename InstructionSequenceExec::instruction::ADD_ACC>(
            &i->v());
    return std::make_shared<InstructionSequenceExec::state>(
        state{s->pc_, (s->acc_ + _m.d_a0)});
  }
}

std::shared_ptr<InstructionSequenceExec::state>
InstructionSequenceExec::exec_program(
    const std::shared_ptr<
        List<std::shared_ptr<InstructionSequenceExec::instruction>>> &prog,
    std::shared_ptr<InstructionSequenceExec::state> s) {
  if (std::holds_alternative<typename List<
          std::shared_ptr<InstructionSequenceExec::instruction>>::Nil>(
          prog->v())) {
    return s;
  } else {
    const auto &_m = *std::get_if<typename List<
        std::shared_ptr<InstructionSequenceExec::instruction>>::Cons>(
        &prog->v());
    return exec_program(_m.d_a1, execute(std::move(s), _m.d_a0));
  }
}
