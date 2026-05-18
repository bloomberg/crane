#include "src_uses_pair_value.h"

uint64_t SrcUsesPairValue::get_reg(const SrcUsesPairValue::state &s,
                                   uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

uint64_t SrcUsesPairValue::get_reg_pair(const SrcUsesPairValue::state &s,
                                        uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

SrcUsesPairValue::state
SrcUsesPairValue::execute_src(const SrcUsesPairValue::state &s, uint64_t r) {
  uint64_t pair_val = get_reg_pair(s, r);
  uint64_t hi = (UINT64_C(16) ? pair_val / UINT64_C(16) : 0);
  return state{s.regs, hi, (UINT64_C(4) ? hi / UINT64_C(4) : 0),
               (UINT64_C(4) ? hi % UINT64_C(4) : hi),
               (UINT64_C(16) ? pair_val % UINT64_C(16) : pair_val)};
}
