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
  unsigned int hi = (16u ? pair_val / 16u : 0);
  return std::make_shared<SrcUsesPairValue::state>(
      state{s->regs, hi, (4u ? hi / 4u : 0), (hi % 4u), (pair_val % 16u)});
}
