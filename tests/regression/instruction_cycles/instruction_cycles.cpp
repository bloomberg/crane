#include <instruction_cycles.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int InstructionCycles::cycles_jms(
    const std::shared_ptr<InstructionCycles::state2> &_x,
    const std::shared_ptr<InstructionCycles::instruction2> &i) {
  return std::visit(
      Overloaded{[](const typename InstructionCycles::instruction2::JMS2 _args)
                     -> unsigned int { return 24u; },
                 [](const typename InstructionCycles::instruction2::NOP2 _args)
                     -> unsigned int { return 8u; }},
      i->v());
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles_min(const InstructionCycles::Instr3 i) {
  switch (i) {
  case Instr3::e_NOP3: {
    return 8u;
  }
  case Instr3::e_ADD3: {
    return 8u;
  }
  case Instr3::e_WRM3: {
    return 8u;
  }
  case Instr3::e_FIM3: {
    return 16u;
  }
  case Instr3::e_JMS3: {
    return 24u;
  }
  case Instr3::e_JCNTAKEN3: {
    return 16u;
  }
  case Instr3::e_JCNNOTTAKEN3: {
    return 8u;
  }
  case Instr3::e_ISZTAKEN3: {
    return 16u;
  }
  case Instr3::e_ISZZERO3: {
    return 8u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles_max(const InstructionCycles::Instr4 i) {
  switch (i) {
  case Instr4::e_NOP4: {
    return 8u;
  }
  case Instr4::e_ADD4: {
    return 8u;
  }
  case Instr4::e_WRM4: {
    return 8u;
  }
  case Instr4::e_FIM4: {
    return 16u;
  }
  case Instr4::e_JMS4: {
    return 24u;
  }
  case Instr4::e_JCNTAKEN4: {
    return 16u;
  }
  case Instr4::e_JCNNOTTAKEN4: {
    return 8u;
  }
  case Instr4::e_ISZTAKEN4: {
    return 16u;
  }
  case Instr4::e_ISZZERO4: {
    return 8u;
  }
  default:
    std::unreachable();
  }
}

std::shared_ptr<InstructionCycles::state5> InstructionCycles::execute5(
    std::shared_ptr<InstructionCycles::state5> s,
    const std::shared_ptr<InstructionCycles::instruction5> &i) {
  return std::visit(
      Overloaded{[&](const typename InstructionCycles::instruction5::NOP5 _args)
                     -> std::shared_ptr<InstructionCycles::state5> {
                   return std::move(s);
                 },
                 [&](const typename InstructionCycles::instruction5::JCN5 _args)
                     -> std::shared_ptr<InstructionCycles::state5> {
                   return std::move(s);
                 },
                 [&](const typename InstructionCycles::instruction5::INC5 _args)
                     -> std::shared_ptr<InstructionCycles::state5> {
                   return std::make_shared<InstructionCycles::state5>(
                       state5{((s->acc5 + 1u) % 16u), s->carry5, s->test5});
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
              std::shared_ptr<InstructionCycles::instruction5>>::Nil _args)
              -> unsigned int { return 0u; },
          [&](const typename List<
              std::shared_ptr<InstructionCycles::instruction5>>::Cons _args)
              -> unsigned int {
            return (_args.d_a0->cycles_sum(s) +
                    program_cycles5(execute5(s, _args.d_a0), _args.d_a1));
          }},
      prog->v());
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles6(const std::shared_ptr<InstructionCycles::state6> &_x,
                           const InstructionCycles::Instruction6 _x0) {
  return 8u;
}

__attribute__((pure)) unsigned int InstructionCycles::program_cycles6(
    const std::shared_ptr<InstructionCycles::state6> &s,
    const std::shared_ptr<List<InstructionCycles::Instruction6>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<InstructionCycles::Instruction6>::Nil _args)
              -> unsigned int { return 0u; },
          [&](const typename List<InstructionCycles::Instruction6>::Cons _args)
              -> unsigned int {
            return (cycles6(s, _args.d_a0) + program_cycles6(s, _args.d_a1));
          }},
      prog->v());
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles7(const std::shared_ptr<InstructionCycles::state7> &_x,
                           const InstructionCycles::Instruction7 _x0) {
  return 8u;
}

__attribute__((pure)) unsigned int InstructionCycles::program_cycles7(
    const std::shared_ptr<InstructionCycles::state7> &s,
    const std::shared_ptr<List<InstructionCycles::Instruction7>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<InstructionCycles::Instruction7>::Nil _args)
              -> unsigned int { return 0u; },
          [&](const typename List<InstructionCycles::Instruction7>::Cons _args)
              -> unsigned int {
            return (cycles7(s, _args.d_a0) + program_cycles7(s, _args.d_a1));
          }},
      prog->v());
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
