#include <algorithm>
#include <any>
#include <cassert>
#include <decode_jms_wf_behavior_0060.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int DecodeJmsWfBehavior0060::acc(
    const std::shared_ptr<DecodeJmsWfBehavior0060::state> &s) {
  return s->acc;
}

bool DecodeJmsWfBehavior0060::carry(
    const std::shared_ptr<DecodeJmsWfBehavior0060::state> &s) {
  return s->carry;
}

bool DecodeJmsWfBehavior0060::test_pin(
    const std::shared_ptr<DecodeJmsWfBehavior0060::state> &s) {
  return s->test_pin;
}

bool DecodeJmsWfBehavior0060::jcn_condition(
    const std::shared_ptr<DecodeJmsWfBehavior0060::state> &s,
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
