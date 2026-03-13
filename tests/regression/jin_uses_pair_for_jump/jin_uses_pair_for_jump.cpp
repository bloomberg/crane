#include <jin_uses_pair_for_jump.h>

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
JinUsesPairForJump::get_reg(const std::shared_ptr<JinUsesPairForJump::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0u);
}

__attribute__((pure)) unsigned int JinUsesPairForJump::get_reg_pair(
    const std::shared_ptr<JinUsesPairForJump::state> &s, const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

__attribute__((pure)) unsigned int
JinUsesPairForJump::page_of(const unsigned int addr) {
  return Nat::div(addr, 256u);
}

std::shared_ptr<JinUsesPairForJump::state>
JinUsesPairForJump::execute_jin(std::shared_ptr<JinUsesPairForJump::state> s,
                                const unsigned int r) {
  unsigned int next_page = page_of((std::move(s)->pc + 1u));
  unsigned int pair_val = get_reg_pair(std::move(s), r);
  return std::make_shared<JinUsesPairForJump::state>(
      state{std::move(s)->regs,
            ((std::move(next_page) * 256u) + (std::move(pair_val) % 256u))});
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
