#include <src_uses_pair_value.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
SrcUsesPairValue::get_reg(const SrcUsesPairValue::state &s,
                          const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.regs, 0u);
}

__attribute__((pure)) unsigned int
SrcUsesPairValue::get_reg_pair(const SrcUsesPairValue::state &s,
                               const unsigned int &r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

__attribute__((pure)) SrcUsesPairValue::state
SrcUsesPairValue::execute_src(const SrcUsesPairValue::state &s,
                              const unsigned int &r) {
  unsigned int pair_val = get_reg_pair(s, r);
  unsigned int hi = (16u ? pair_val / 16u : 0);
  return state{s.regs, hi, (4u ? hi / 4u : 0), (4u ? hi % 4u : hi),
               (16u ? pair_val % 16u : pair_val)};
}
