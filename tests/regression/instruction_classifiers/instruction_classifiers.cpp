#include <instruction_classifiers.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
            return ([&]() {
              if (_args.d_a0->writes_acc()) {
                return 1u;
              } else {
                return 0u;
              }
            }() + count_writes_acc(_args.d_a1));
          }},
      prog->v());
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
            return ([&]() {
              if (_args.d_a0->writes_ram()) {
                return 1u;
              } else {
                return 0u;
              }
            }() + count_writes_ram(_args.d_a1));
          }},
      prog->v());
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
            return ([&]() {
              if (_args.d_a0->writes_regs()) {
                return 1u;
              } else {
                return 0u;
              }
            }() + count_writes_regs(_args.d_a1));
          }},
      prog->v());
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
            return ([&]() {
              if (_args.d_a0->is_jump()) {
                return 1u;
              } else {
                return 0u;
              }
            }() + count_jumps(_args.d_a1));
          }},
      prog->v());
}
