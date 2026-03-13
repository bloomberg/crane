#include <jcn_ops.h>

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

__attribute__((pure)) bool
JcnOps::jcn_condition(const std::shared_ptr<JcnOps::state> &s,
                      const unsigned int cond) {
  unsigned int c1 = Nat::div(cond, 8u);
  unsigned int c2 = (Nat::div(cond, 4u) % 2u);
  unsigned int c3 = (Nat::div(cond, 2u) % 2u);
  unsigned int c4 = (cond % 2u);
  bool base = ((s->acc == 0u && std::move(c2) == 1u) ||
               ((s->carry && std::move(c3) == 1u) ||
                (!(s->test_pin) && std::move(c4) == 1u)));
  if (std::move(c1) == 1u) {
    return !(std::move(base));
  } else {
    return std::move(base);
  }
}

__attribute__((pure)) unsigned int JcnOps::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

__attribute__((pure)) unsigned int
JcnOps::pc_inc2(const std::shared_ptr<JcnOps::state> &s) {
  return addr12_of_nat((s->pc + 2u));
}

__attribute__((pure)) unsigned int JcnOps::page_of(const unsigned int p) {
  return Nat::div(p, 256u);
}

__attribute__((pure)) unsigned int JcnOps::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

__attribute__((pure)) unsigned int
JcnOps::base_for_next2(const std::shared_ptr<JcnOps::state> &s) {
  return page_base(pc_inc2(s));
}

__attribute__((pure)) unsigned int
JcnOps::branch_target(const std::shared_ptr<JcnOps::state> &s,
                      const unsigned int cond, const unsigned int off) {
  if (jcn_condition(s, cond)) {
    return addr12_of_nat((base_for_next2(s) + off));
  } else {
    return addr12_of_nat((s->pc + 2u));
  }
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
