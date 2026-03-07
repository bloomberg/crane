#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <jcn_condition_test_high.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int JcnConditionTestHigh::acc(
    const std::shared_ptr<JcnConditionTestHigh::state> &s) {
  return s->acc;
}

bool JcnConditionTestHigh::carry(
    const std::shared_ptr<JcnConditionTestHigh::state> &s) {
  return s->carry;
}

bool JcnConditionTestHigh::test_pin(
    const std::shared_ptr<JcnConditionTestHigh::state> &s) {
  return s->test_pin;
}

bool JcnConditionTestHigh::jcn_condition(
    const std::shared_ptr<JcnConditionTestHigh::state> &s,
    const unsigned int cond) {
  unsigned int c1 =
      Nat::div(cond, ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  unsigned int c2 = (Nat::div(cond, ((((0 + 1) + 1) + 1) + 1)) % ((0 + 1) + 1));
  unsigned int c3 = (Nat::div(cond, ((0 + 1) + 1)) % ((0 + 1) + 1));
  unsigned int c4 = (cond % ((0 + 1) + 1));
  bool base = (((s->acc == 0) && (std::move(c2) == (0 + 1))) ||
               ((s->carry && (std::move(c3) == (0 + 1))) ||
                (!(s->test_pin) && (std::move(c4) == (0 + 1)))));
  if ((c1 == (0 + 1))) {
    return !(std::move(base));
  } else {
    return std::move(base);
  }
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
