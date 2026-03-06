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

unsigned int InstructionCycleSum::acc_(
    const std::shared_ptr<InstructionCycleSum::state> &s) {
  return s->acc_;
}

bool InstructionCycleSum::carry_(
    const std::shared_ptr<InstructionCycleSum::state> &s) {
  return s->carry_;
}

bool InstructionCycleSum::test_(
    const std::shared_ptr<InstructionCycleSum::state> &s) {
  return s->test_;
}

unsigned int InstructionCycleSum::cycles(
    const std::shared_ptr<InstructionCycleSum::state> &s,
    const std::shared_ptr<InstructionCycleSum::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename InstructionCycleSum::instruction::NOP_ _args)
              -> unsigned int {
            return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
          },
          [&](const typename InstructionCycleSum::instruction::JCN_ _args)
              -> unsigned int {
            unsigned int n = _args._a0;
            if ((Nat::div(n, ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                              1)) == (0 + 1))) {
              return ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1);
            } else {
              if (((s->acc_ == 0) && ((Nat::div(n, ((((0 + 1) + 1) + 1) + 1)) %
                                       ((0 + 1) + 1)) == (0 + 1)))) {
                return (
                    (((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1);
              } else {
                return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
              }
            }
          },
          [](const typename InstructionCycleSum::instruction::INC_ _args)
              -> unsigned int {
            return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
          }},
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
            return std::make_shared<InstructionCycleSum::state>(state{
                ((s->acc_ + (0 + 1)) %
                 ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1)),
                s->carry_, s->test_});
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
              -> unsigned int { return 0; },
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
    return Nat::divmod(x, y_, 0, y_).first;
  }
}
