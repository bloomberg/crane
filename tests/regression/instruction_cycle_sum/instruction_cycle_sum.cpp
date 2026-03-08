#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <instruction_cycle_sum.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int InstructionCycleSum::cycles(
    const std::shared_ptr<InstructionCycleSum::state> &s,
    const std::shared_ptr<InstructionCycleSum::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename InstructionCycleSum::instruction::NOP_ _args)
              -> unsigned int { return 8u; },
          [&](const typename InstructionCycleSum::instruction::JCN_ _args)
              -> unsigned int {
            unsigned int n = _args._a0;
            if ((Nat::div(n, 8u) == 1u)) {
              return 16u;
            } else {
              if (((s->acc_ == 0u) && ((Nat::div(n, 4u) % 2u) == 1u))) {
                return 16u;
              } else {
                return 8u;
              }
            }
          },
          [](const typename InstructionCycleSum::instruction::INC_ _args)
              -> unsigned int { return 8u; }},
      i->v());
}

std::shared_ptr<InstructionCycleSum::state> InstructionCycleSum::execute(
    std::shared_ptr<InstructionCycleSum::state> s,
    const std::shared_ptr<InstructionCycleSum::instruction> &i) {
  return std::visit(
      Overloaded{
          [&](const typename InstructionCycleSum::instruction::NOP_ _args)
              -> std::shared_ptr<InstructionCycleSum::state> {
            return std::move(s);
          },
          [&](const typename InstructionCycleSum::instruction::JCN_ _args)
              -> std::shared_ptr<InstructionCycleSum::state> {
            return std::move(s);
          },
          [&](const typename InstructionCycleSum::instruction::INC_ _args)
              -> std::shared_ptr<InstructionCycleSum::state> {
            return std::make_shared<InstructionCycleSum::state>(
                state{((s->acc_ + 1u) % 16u), s->carry_, s->test_});
          }},
      i->v());
}

unsigned int InstructionCycleSum::program_cycles(
    const std::shared_ptr<InstructionCycleSum::state> &s,
    const std::shared_ptr<
        List<std::shared_ptr<InstructionCycleSum::instruction>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<InstructionCycleSum::instruction>>::nil _args)
              -> unsigned int { return 0u; },
          [&](const typename List<
              std::shared_ptr<InstructionCycleSum::instruction>>::cons _args)
              -> unsigned int {
            std::shared_ptr<InstructionCycleSum::instruction> i = _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<InstructionCycleSum::instruction>>>
                rest = _args._a1;
            return (cycles(s, i) +
                    program_cycles(execute(s, i), std::move(rest)));
          }},
      prog->v());
}

std::pair<unsigned int, unsigned int> Nat::divmod(const unsigned int x,
                                                  const unsigned int y,
                                                  const unsigned int q,
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

unsigned int Nat::div(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
