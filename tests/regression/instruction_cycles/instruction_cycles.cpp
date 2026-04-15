#include <instruction_cycles.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int InstructionCycles::cycles_jms(
    const std::shared_ptr<InstructionCycles::state2> &,
    const std::shared_ptr<InstructionCycles::instruction2> &i) {
  if (std::holds_alternative<typename InstructionCycles::instruction2::JMS2>(
          i->v())) {
    return 24u;
  } else {
    return 8u;
  }
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles_min(const InstructionCycles::Instr3 i) {
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

__attribute__((pure)) unsigned int
InstructionCycles::cycles_max(const InstructionCycles::Instr4 i) {
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

std::shared_ptr<InstructionCycles::state5> InstructionCycles::execute5(
    std::shared_ptr<InstructionCycles::state5> s,
    const std::shared_ptr<InstructionCycles::instruction5> &i) {
  if (std::holds_alternative<typename InstructionCycles::instruction5::INC5>(
          i->v())) {
    return std::make_shared<InstructionCycles::state5>(state5{
        (16u ? (s->acc5 + 1u) % 16u : (s->acc5 + 1u)), s->carry5, s->test5});
  } else {
    return s;
  }
}

__attribute__((pure)) unsigned int InstructionCycles::program_cycles5(
    const std::shared_ptr<InstructionCycles::state5> &s,
    const std::shared_ptr<
        List<std::shared_ptr<InstructionCycles::instruction5>>> &prog) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<InstructionCycles::instruction5>>::Nil>(
          prog->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<
        typename List<std::shared_ptr<InstructionCycles::instruction5>>::Cons>(
        &prog->v());
    return (_m.d_a0->cycles_sum(s) +
            program_cycles5(execute5(s, _m.d_a0), _m.d_a1));
  }
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles6(const std::shared_ptr<InstructionCycles::state6> &,
                           const InstructionCycles::Instruction6) {
  return 8u;
}

__attribute__((pure)) unsigned int InstructionCycles::program_cycles6(
    const std::shared_ptr<InstructionCycles::state6> &s,
    const std::shared_ptr<List<InstructionCycles::Instruction6>> &prog) {
  if (std::holds_alternative<
          typename List<InstructionCycles::Instruction6>::Nil>(prog->v())) {
    return 0u;
  } else {
    const auto &_m =
        *std::get_if<typename List<InstructionCycles::Instruction6>::Cons>(
            &prog->v());
    return (cycles6(s, _m.d_a0) + program_cycles6(s, _m.d_a1));
  }
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles7(const std::shared_ptr<InstructionCycles::state7> &,
                           const InstructionCycles::Instruction7) {
  return 8u;
}

__attribute__((pure)) unsigned int InstructionCycles::program_cycles7(
    const std::shared_ptr<InstructionCycles::state7> &s,
    const std::shared_ptr<List<InstructionCycles::Instruction7>> &prog) {
  if (std::holds_alternative<
          typename List<InstructionCycles::Instruction7>::Nil>(prog->v())) {
    return 0u;
  } else {
    const auto &_m =
        *std::get_if<typename List<InstructionCycles::Instruction7>::Cons>(
            &prog->v());
    return (cycles7(s, _m.d_a0) + program_cycles7(s, _m.d_a1));
  }
}
