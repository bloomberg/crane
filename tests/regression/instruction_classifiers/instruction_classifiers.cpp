#include <instruction_classifiers.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) bool InstructionClassifiers::writes_acc(
    const std::shared_ptr<InstructionClassifiers::instr_acc> &i) {
  return std::visit(
      Overloaded{
          [](const typename InstructionClassifiers::instr_acc::LDM _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::LD _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::ADD _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::SUB _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::INC _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::XCH _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::BBL _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::SBM _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::RDM _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::RDR _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::ADM _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::RD0 _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::RD1 _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::RD2 _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::RD3 _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::CLB _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::CMA _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::IAC _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::DAC _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::RAL _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::RAR _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::TCC _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::TCS _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::DAA _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::KBP _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_acc::NOP_acc _args)
              -> bool { return false; }},
      i->v());
}

__attribute__((pure)) unsigned int InstructionClassifiers::count_writes_acc(
    const std::shared_ptr<
        List<std::shared_ptr<InstructionClassifiers::instr_acc>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<InstructionClassifiers::instr_acc>>::Nil _args)
              -> unsigned int { return 0u; },
          [](const typename List<
              std::shared_ptr<InstructionClassifiers::instr_acc>>::Cons _args)
              -> unsigned int {
            std::shared_ptr<InstructionClassifiers::instr_acc> i = _args.d_a0;
            std::shared_ptr<
                List<std::shared_ptr<InstructionClassifiers::instr_acc>>>
                rest = _args.d_a1;
            return ([&](void) {
              if (writes_acc(std::move(i))) {
                return 1u;
              } else {
                return 0u;
              }
            }() + count_writes_acc(std::move(rest)));
          }},
      prog->v());
}

__attribute__((pure)) bool InstructionClassifiers::writes_ram(
    const std::shared_ptr<InstructionClassifiers::instr_ram> &i) {
  return std::visit(
      Overloaded{
          [](const typename InstructionClassifiers::instr_ram::WRM _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_ram::WMP _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_ram::WR0 _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_ram::WR1 _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_ram::WR2 _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_ram::WR3 _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_ram::NOP_ram _args)
              -> bool { return false; },
          [](const typename InstructionClassifiers::instr_ram::ADD_ram _args)
              -> bool { return false; }},
      i->v());
}

__attribute__((pure)) unsigned int InstructionClassifiers::count_writes_ram(
    const std::shared_ptr<
        List<std::shared_ptr<InstructionClassifiers::instr_ram>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<InstructionClassifiers::instr_ram>>::Nil _args)
              -> unsigned int { return 0u; },
          [](const typename List<
              std::shared_ptr<InstructionClassifiers::instr_ram>>::Cons _args)
              -> unsigned int {
            std::shared_ptr<InstructionClassifiers::instr_ram> i = _args.d_a0;
            std::shared_ptr<
                List<std::shared_ptr<InstructionClassifiers::instr_ram>>>
                rest = _args.d_a1;
            return ([&](void) {
              if (writes_ram(std::move(i))) {
                return 1u;
              } else {
                return 0u;
              }
            }() + count_writes_ram(std::move(rest)));
          }},
      prog->v());
}

__attribute__((pure)) bool InstructionClassifiers::writes_regs(
    const std::shared_ptr<InstructionClassifiers::instr_regs> &i) {
  return std::visit(
      Overloaded{
          [](const typename InstructionClassifiers::instr_regs::XCH_regs _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_regs::INC_regs _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_regs::FIM _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_regs::FIN _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_regs::ISZ _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_regs::NOP_regs _args)
              -> bool { return false; },
          [](const typename InstructionClassifiers::instr_regs::ADD_regs _args)
              -> bool { return false; }},
      i->v());
}

__attribute__((pure)) unsigned int InstructionClassifiers::count_writes_regs(
    const std::shared_ptr<
        List<std::shared_ptr<InstructionClassifiers::instr_regs>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<InstructionClassifiers::instr_regs>>::Nil _args)
              -> unsigned int { return 0u; },
          [](const typename List<
              std::shared_ptr<InstructionClassifiers::instr_regs>>::Cons _args)
              -> unsigned int {
            std::shared_ptr<InstructionClassifiers::instr_regs> i = _args.d_a0;
            std::shared_ptr<
                List<std::shared_ptr<InstructionClassifiers::instr_regs>>>
                rest = _args.d_a1;
            return ([&](void) {
              if (writes_regs(std::move(i))) {
                return 1u;
              } else {
                return 0u;
              }
            }() + count_writes_regs(std::move(rest)));
          }},
      prog->v());
}

__attribute__((pure)) bool InstructionClassifiers::is_jump(
    const std::shared_ptr<InstructionClassifiers::instr_jump> &i) {
  return std::visit(
      Overloaded{
          [](const typename InstructionClassifiers::instr_jump::JCN _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_jump::JUN _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_jump::JMS _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_jump::JIN _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_jump::BBL_jump _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_jump::ISZ_jump _args)
              -> bool { return true; },
          [](const typename InstructionClassifiers::instr_jump::ADD_jump _args)
              -> bool { return false; },
          [](const typename InstructionClassifiers::instr_jump::NOP_jump _args)
              -> bool { return false; }},
      i->v());
}

__attribute__((pure)) unsigned int InstructionClassifiers::count_jumps(
    const std::shared_ptr<
        List<std::shared_ptr<InstructionClassifiers::instr_jump>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<InstructionClassifiers::instr_jump>>::Nil _args)
              -> unsigned int { return 0u; },
          [](const typename List<
              std::shared_ptr<InstructionClassifiers::instr_jump>>::Cons _args)
              -> unsigned int {
            std::shared_ptr<InstructionClassifiers::instr_jump> i = _args.d_a0;
            std::shared_ptr<
                List<std::shared_ptr<InstructionClassifiers::instr_jump>>>
                rest = _args.d_a1;
            return ([&](void) {
              if (is_jump(std::move(i))) {
                return 1u;
              } else {
                return 0u;
              }
            }() + count_jumps(std::move(rest)));
          }},
      prog->v());
}
