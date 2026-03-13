#include <instruction_cycles.h>

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

__attribute__((pure)) unsigned int InstructionCycles::cycles_jcn(
    const std::shared_ptr<InstructionCycles::state1> &s,
    const std::shared_ptr<InstructionCycles::instruction1> &i) {
  return std::visit(
      Overloaded{[&](const typename InstructionCycles::instruction1::JCN1 _args)
                     -> unsigned int {
                   unsigned int cond = _args.d_a0;
                   unsigned int c1 = Nat::div(std::move(cond), 8u);
                   unsigned int c2 = (Nat::div(std::move(cond), 4u) % 2u);
                   unsigned int c3 = (Nat::div(std::move(cond), 2u) % 2u);
                   unsigned int c4 = (std::move(cond) % 2u);
                   bool base_cond =
                       ((s->acc1 == 0u && std::move(c2) == 1u) ||
                        ((s->carry1 && std::move(c3) == 1u) ||
                         (!(s->test_pin1) && std::move(c4) == 1u)));
                   bool jump;
                   if (std::move(c1) == 1u) {
                     jump = !(std::move(base_cond));
                   } else {
                     jump = std::move(base_cond);
                   }
                   if (std::move(jump)) {
                     return 16u;
                   } else {
                     return 8u;
                   }
                 },
                 [](const typename InstructionCycles::instruction1::NOP1 _args)
                     -> unsigned int { return 8u; }},
      i->v());
}

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
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) unsigned int
InstructionCycles::cycles_max(const InstructionCycles::Instr4 i) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) unsigned int InstructionCycles::cycles_sum(
    const std::shared_ptr<InstructionCycles::state5> &s,
    const std::shared_ptr<InstructionCycles::instruction5> &i) {
  return std::visit(
      Overloaded{[](const typename InstructionCycles::instruction5::NOP5 _args)
                     -> unsigned int { return 8u; },
                 [&](const typename InstructionCycles::instruction5::JCN5 _args)
                     -> unsigned int {
                   unsigned int n = _args.d_a0;
                   if (Nat::div(n, 8u) == 1u) {
                     return 16u;
                   } else {
                     if ((s->acc5 == 0u &&
                          (Nat::div(std::move(n), 4u) % 2u) == 1u)) {
                       return 16u;
                     } else {
                       return 8u;
                     }
                   }
                 },
                 [](const typename InstructionCycles::instruction5::INC5 _args)
                     -> unsigned int { return 8u; }},
      i->v());
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
            std::shared_ptr<InstructionCycles::instruction5> i = _args.d_a0;
            std::shared_ptr<
                List<std::shared_ptr<InstructionCycles::instruction5>>>
                rest = _args.d_a1;
            return (cycles_sum(s, i) +
                    program_cycles5(execute5(s, i), std::move(rest)));
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
            InstructionCycles::Instruction6 i = _args.d_a0;
            std::shared_ptr<List<InstructionCycles::Instruction6>> rest =
                _args.d_a1;
            return (cycles6(s, i) + program_cycles6(s, std::move(rest)));
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
            InstructionCycles::Instruction7 i = _args.d_a0;
            std::shared_ptr<List<InstructionCycles::Instruction7>> rest =
                _args.d_a1;
            return (cycles7(s, i) + program_cycles7(s, std::move(rest)));
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
