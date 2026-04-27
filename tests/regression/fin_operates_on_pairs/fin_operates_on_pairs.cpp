#include <fin_operates_on_pairs.h>

__attribute__((pure)) unsigned int
FinOperatesOnPairs::get_reg(const FinOperatesOnPairs::state &s,
                            const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.regs, 0u);
}

__attribute__((pure)) FinOperatesOnPairs::state
FinOperatesOnPairs::set_reg(const FinOperatesOnPairs::state &s,
                            const unsigned int &r, const unsigned int &v) {
  return state{update_nth<unsigned int>(r, (16u ? v % 16u : v), s.regs), s.rom};
}

__attribute__((pure)) unsigned int
FinOperatesOnPairs::get_reg_pair(const FinOperatesOnPairs::state &s,
                                 const unsigned int &r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

__attribute__((pure)) FinOperatesOnPairs::state
FinOperatesOnPairs::set_reg_pair(const FinOperatesOnPairs::state &s,
                                 const unsigned int &r, const unsigned int &v) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  unsigned int hi = (16u ? v / 16u : 0);
  unsigned int lo = (16u ? v % 16u : v);
  FinOperatesOnPairs::state s1 = set_reg(s, base, hi);
  return set_reg(s1, (base + 1u), lo);
}

__attribute__((pure)) FinOperatesOnPairs::state
FinOperatesOnPairs::execute_fin(const FinOperatesOnPairs::state &s,
                                const unsigned int &r) {
  return set_reg_pair(
      s, r,
      ListDef::template nth<unsigned int>(get_reg_pair(s, 0u), s.rom, 0u));
}
