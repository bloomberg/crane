#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <instruction_sequence_exec.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int InstructionSequenceExec::pc_(
    const std::shared_ptr<InstructionSequenceExec::state> &s) {
  return s->pc_;
}

unsigned int InstructionSequenceExec::acc_(
    const std::shared_ptr<InstructionSequenceExec::state> &s) {
  return s->acc_;
}

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
            unsigned int n = _args._a0;
            return std::make_shared<InstructionSequenceExec::state>(
                state{s->pc_, (s->acc_ + std::move(n))});
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
              std::shared_ptr<InstructionSequenceExec::instruction>>::nil _args)
              -> std::shared_ptr<InstructionSequenceExec::state> {
            return std::move(s);
          },
          [&](const typename List<
              std::shared_ptr<InstructionSequenceExec::instruction>>::cons
                  _args) -> std::shared_ptr<InstructionSequenceExec::state> {
            std::shared_ptr<InstructionSequenceExec::instruction> i = _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<InstructionSequenceExec::instruction>>>
                rest = _args._a1;
            return exec_program(std::move(rest),
                                execute(std::move(s), std::move(i)));
          }},
      prog->v());
}
