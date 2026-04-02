#include <src_uses_pair_value.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
SrcUsesPairValue::get_reg(const std::shared_ptr<SrcUsesPairValue::state> &s,
                          const unsigned int r) {
  return s->regs->nth(r, 0u);
}

__attribute__((pure)) unsigned int SrcUsesPairValue::get_reg_pair(
    const std::shared_ptr<SrcUsesPairValue::state> &s, const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<SrcUsesPairValue::state>
SrcUsesPairValue::execute_src(std::shared_ptr<SrcUsesPairValue::state> s,
                              const unsigned int r) {
  unsigned int pair_val = get_reg_pair(s, r);
  unsigned int hi = Nat::div(pair_val, 16u);
  return std::make_shared<SrcUsesPairValue::state>(
      state{s->regs, hi, Nat::div(hi, 4u), (hi % 4u), (pair_val % 16u)});
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(q, u);
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
