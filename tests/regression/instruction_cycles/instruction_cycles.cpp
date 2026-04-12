#include <instruction_cycles.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int InstructionCycles::cycles_jms(
    const std::shared_ptr<InstructionCycles::state2> &,
    const std::shared_ptr<InstructionCycles::instruction2> &i) {
  return std::visit(
      Overloaded{[](const typename InstructionCycles::instruction2::JMS2 &)
                     -> unsigned int { return 24u; },
                 [](const typename InstructionCycles::instruction2::NOP2 &)
                     -> unsigned int { return 8u; }},
      i->v());
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
  return std::visit(
      Overloaded{
          [&](const typename InstructionCycles::instruction5::INC5 &)
              -> std::shared_ptr<InstructionCycles::state5> {
            return std::make_shared<InstructionCycles::state5>(
                state5{(16u ? (s->acc5 + 1u) % 16u : (s->acc5 + 1u)), s->carry5,
                       s->test5});
          },
          [&](const auto &) -> std::shared_ptr<InstructionCycles::state5> {
            return s;
          }},
      i->v());
}

__attribute__((pure)) unsigned int InstructionCycles::program_cycles5(
    const std::shared_ptr<InstructionCycles::state5> &s,
    const std::shared_ptr<
        List<std::shared_ptr<InstructionCycles::instruction5>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<InstructionCycles::instruction5>>::Nil &)
              -> unsigned int { return 0u; },
          [&](const typename List<
              std::shared_ptr<InstructionCycles::instruction5>>::Cons &_args)
              -> unsigned int {
            return (_args.d_a0->cycles_sum(s) +
                    program_cycles5(execute5(s, _args.d_a0), _args.d_a1));
          }},
      prog->v());
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles6(const std::shared_ptr<InstructionCycles::state6> &,
                           const InstructionCycles::Instruction6) {
  return 8u;
}

__attribute__((pure)) unsigned int InstructionCycles::program_cycles6(
    const std::shared_ptr<InstructionCycles::state6> &s,
    const std::shared_ptr<List<InstructionCycles::Instruction6>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<InstructionCycles::Instruction6>::Nil &)
              -> unsigned int { return 0u; },
          [&](const typename List<InstructionCycles::Instruction6>::Cons &_args)
              -> unsigned int {
            return (cycles6(s, _args.d_a0) + program_cycles6(s, _args.d_a1));
          }},
      prog->v());
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles7(const std::shared_ptr<InstructionCycles::state7> &,
                           const InstructionCycles::Instruction7) {
  return 8u;
}

__attribute__((pure)) unsigned int InstructionCycles::program_cycles7(
    const std::shared_ptr<InstructionCycles::state7> &s,
    const std::shared_ptr<List<InstructionCycles::Instruction7>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<InstructionCycles::Instruction7>::Nil &)
              -> unsigned int { return 0u; },
          [&](const typename List<InstructionCycles::Instruction7>::Cons &_args)
              -> unsigned int {
            return (cycles7(s, _args.d_a0) + program_cycles7(s, _args.d_a1));
          }},
      prog->v());
}
