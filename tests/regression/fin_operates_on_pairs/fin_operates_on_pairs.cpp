#include <fin_operates_on_pairs.h>

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

__attribute__((pure)) unsigned int
FinOperatesOnPairs::get_reg(const std::shared_ptr<FinOperatesOnPairs::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0u);
}

std::shared_ptr<FinOperatesOnPairs::state>
FinOperatesOnPairs::set_reg(std::shared_ptr<FinOperatesOnPairs::state> s,
                            const unsigned int r, const unsigned int v) {
  return std::make_shared<FinOperatesOnPairs::state>(state{
      update_nth<unsigned int>(std::move(r), (std::move(v) % 16u), s->regs),
      s->rom});
}

__attribute__((pure)) unsigned int FinOperatesOnPairs::get_reg_pair(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<FinOperatesOnPairs::state> FinOperatesOnPairs::set_reg_pair(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r,
    const unsigned int v) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  unsigned int hi = Nat::div(v, 16u);
  unsigned int lo = (v % 16u);
  std::shared_ptr<FinOperatesOnPairs::state> s1 =
      set_reg(s, std::move(base), std::move(hi));
  return set_reg(std::move(s1), (std::move(base) + 1u), std::move(lo));
}

std::shared_ptr<FinOperatesOnPairs::state> FinOperatesOnPairs::execute_fin(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r) {
  return set_reg_pair(s, r, s->rom->nth(get_reg_pair(s, 0u), 0u));
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
