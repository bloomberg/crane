#include <algorithm>
#include <any>
#include <cassert>
#include <cycles_jcn_not_taken.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int
CyclesJcnNotTaken::acc(const std::shared_ptr<CyclesJcnNotTaken::state> &s) {
  return s->acc;
}

bool CyclesJcnNotTaken::carry(
    const std::shared_ptr<CyclesJcnNotTaken::state> &s) {
  return s->carry;
}

bool CyclesJcnNotTaken::test_pin(
    const std::shared_ptr<CyclesJcnNotTaken::state> &s) {
  return s->test_pin;
}

unsigned int CyclesJcnNotTaken::cycles(
    const std::shared_ptr<CyclesJcnNotTaken::state> &s,
    const std::shared_ptr<CyclesJcnNotTaken::instruction> &i) {
  return std::visit(
      Overloaded{
          [&](const typename CyclesJcnNotTaken::instruction::JCN _args)
              -> unsigned int {
            unsigned int cond = _args._a0;
            unsigned int c1 =
                Nat::div(std::move(cond),
                         ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
            unsigned int c2 =
                (Nat::div(std::move(cond), ((((0 + 1) + 1) + 1) + 1)) %
                 ((0 + 1) + 1));
            unsigned int c3 =
                (Nat::div(std::move(cond), ((0 + 1) + 1)) % ((0 + 1) + 1));
            unsigned int c4 = (std::move(cond) % ((0 + 1) + 1));
            bool base_cond = (((s->acc == 0) && (std::move(c2) == (0 + 1))) ||
                              ((s->carry && (std::move(c3) == (0 + 1))) ||
                               (!(s->test_pin) && (std::move(c4) == (0 + 1)))));
            bool jump;
            if ((std::move(c1) == (0 + 1))) {
              jump = !(std::move(base_cond));
            } else {
              jump = std::move(base_cond);
            }
            if (jump) {
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
              return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
            }
          },
          [](const typename CyclesJcnNotTaken::instruction::NOP _args)
              -> unsigned int {
            return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
          }},
      i->v());
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
