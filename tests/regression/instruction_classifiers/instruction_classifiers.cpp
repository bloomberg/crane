#include <instruction_classifiers.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int InstructionClassifiers::count_writes_acc(
    const List<InstructionClassifiers::instr_acc> &prog) {
  if (std::holds_alternative<
          typename List<InstructionClassifiers::instr_acc>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<InstructionClassifiers::instr_acc>::Cons>(
            prog.v());
    return ([&]() -> unsigned int {
      if (d_a0.writes_acc()) {
        return 1u;
      } else {
        return 0u;
      }
    }() + count_writes_acc(*(d_a1)));
  }
}

__attribute__((pure)) unsigned int InstructionClassifiers::count_writes_ram(
    const List<InstructionClassifiers::instr_ram> &prog) {
  if (std::holds_alternative<
          typename List<InstructionClassifiers::instr_ram>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<InstructionClassifiers::instr_ram>::Cons>(
            prog.v());
    return ([&]() -> unsigned int {
      if (d_a0.writes_ram()) {
        return 1u;
      } else {
        return 0u;
      }
    }() + count_writes_ram(*(d_a1)));
  }
}

__attribute__((pure)) unsigned int InstructionClassifiers::count_writes_regs(
    const List<InstructionClassifiers::instr_regs> &prog) {
  if (std::holds_alternative<
          typename List<InstructionClassifiers::instr_regs>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<InstructionClassifiers::instr_regs>::Cons>(
            prog.v());
    return ([&]() -> unsigned int {
      if (d_a0.writes_regs()) {
        return 1u;
      } else {
        return 0u;
      }
    }() + count_writes_regs(*(d_a1)));
  }
}

__attribute__((pure)) unsigned int InstructionClassifiers::count_jumps(
    const List<InstructionClassifiers::instr_jump> &prog) {
  if (std::holds_alternative<
          typename List<InstructionClassifiers::instr_jump>::Nil>(prog.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<InstructionClassifiers::instr_jump>::Cons>(
            prog.v());
    return ([&]() -> unsigned int {
      if (d_a0.is_jump()) {
        return 1u;
      } else {
        return 0u;
      }
    }() + count_jumps(*(d_a1)));
  }
}
