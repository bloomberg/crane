#include "jin_uses_pair_for_jump.h"

uint64_t JinUsesPairForJump::get_reg(const JinUsesPairForJump::state &s,
                                     uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

uint64_t JinUsesPairForJump::get_reg_pair(const JinUsesPairForJump::state &s,
                                          uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

uint64_t JinUsesPairForJump::page_of(uint64_t addr) {
  return (UINT64_C(256) ? addr / UINT64_C(256) : 0);
}

JinUsesPairForJump::state
JinUsesPairForJump::execute_jin(const JinUsesPairForJump::state &s,
                                uint64_t r) {
  uint64_t next_page = page_of((s.pc + UINT64_C(1)));
  uint64_t pair_val = get_reg_pair(s, r);
  return state{s.regs, ((next_page * UINT64_C(256)) +
                        (UINT64_C(256) ? pair_val % UINT64_C(256) : pair_val))};
}
