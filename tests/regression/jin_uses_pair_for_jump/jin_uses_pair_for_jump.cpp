#include <jin_uses_pair_for_jump.h>

__attribute__((pure)) unsigned int
JinUsesPairForJump::get_reg(const JinUsesPairForJump::state &s,
                            const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.regs, 0u);
}

__attribute__((pure)) unsigned int
JinUsesPairForJump::get_reg_pair(const JinUsesPairForJump::state &s,
                                 const unsigned int &r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

__attribute__((pure)) unsigned int
JinUsesPairForJump::page_of(const unsigned int &addr) {
  return (256u ? addr / 256u : 0);
}

__attribute__((pure)) JinUsesPairForJump::state
JinUsesPairForJump::execute_jin(const JinUsesPairForJump::state &s,
                                const unsigned int &r) {
  unsigned int next_page = page_of((s.pc + 1u));
  unsigned int pair_val = get_reg_pair(s, r);
  return state{s.regs,
               ((next_page * 256u) + (256u ? pair_val % 256u : pair_val))};
}
