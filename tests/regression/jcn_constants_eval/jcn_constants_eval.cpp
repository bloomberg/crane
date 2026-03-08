#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <jcn_constants_eval.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

bool JcnConstantsEval::jcn_condition(
    const std::shared_ptr<JcnConstantsEval::state> &s,
    const unsigned int cond) {
  unsigned int c1 = Nat::div(cond, 8u);
  unsigned int c2 = (Nat::div(cond, 4u) % 2u);
  unsigned int c3 = (Nat::div(cond, 2u) % 2u);
  unsigned int c4 = (cond % 2u);
  bool base = (((s->acc == 0u) && (std::move(c2) == 1u)) ||
               ((s->carry && (std::move(c3) == 1u)) ||
                (!(s->test_pin) && (std::move(c4) == 1u))));
  if ((c1 == 1u)) {
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
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
