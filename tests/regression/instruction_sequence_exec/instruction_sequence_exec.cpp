#include <instruction_sequence_exec.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<InstructionSequenceExec::state>
InstructionSequenceExec::execute(
    std::shared_ptr<InstructionSequenceExec::state> s,
    const std::shared_ptr<InstructionSequenceExec::instruction> &i) {
  return std::visit(
      Overloaded{
          [&](const typename InstructionSequenceExec::instruction::NOP_ _args)
              -> std::shared_ptr<InstructionSequenceExec::state> {
            return std::move(s);
          },
          [&](const typename InstructionSequenceExec::instruction::INC_PC _args)
              -> std::shared_ptr<InstructionSequenceExec::state> {
            return std::make_shared<InstructionSequenceExec::state>(
                state{(s->pc_ + 1), s->acc_});
          },
          [&](const typename InstructionSequenceExec::instruction::ADD_ACC
                  _args) -> std::shared_ptr<InstructionSequenceExec::state> {
            return std::make_shared<InstructionSequenceExec::state>(
                state{s->pc_, (s->acc_ + _args.d_a0)});
          }},
      i->v());
}

std::shared_ptr<InstructionSequenceExec::state>
InstructionSequenceExec::exec_program(
    const std::shared_ptr<
        List<std::shared_ptr<InstructionSequenceExec::instruction>>> &prog,
    std::shared_ptr<InstructionSequenceExec::state> s) {
  return std::visit(
      Overloaded{
          [&](const typename List<
              std::shared_ptr<InstructionSequenceExec::instruction>>::Nil _args)
              -> std::shared_ptr<InstructionSequenceExec::state> {
            return std::move(s);
          },
          [&](const typename List<
              std::shared_ptr<InstructionSequenceExec::instruction>>::Cons
                  _args) -> std::shared_ptr<InstructionSequenceExec::state> {
            return exec_program(_args.d_a1, execute(std::move(s), _args.d_a0));
          }},
      prog->v());
}
