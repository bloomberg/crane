#include "fin_operates_on_pairs.h"

uint64_t FinOperatesOnPairs::get_reg(const FinOperatesOnPairs::state &s,
                                     uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

FinOperatesOnPairs::state
FinOperatesOnPairs::set_reg(const FinOperatesOnPairs::state &s, uint64_t r,
                            uint64_t v) {
  return state{
      update_nth<uint64_t>(r, (UINT64_C(16) ? v % UINT64_C(16) : v), s.regs),
      s.rom};
}

uint64_t FinOperatesOnPairs::get_reg_pair(const FinOperatesOnPairs::state &s,
                                          uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

FinOperatesOnPairs::state
FinOperatesOnPairs::set_reg_pair(const FinOperatesOnPairs::state &s, uint64_t r,
                                 uint64_t v) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  uint64_t hi = (UINT64_C(16) ? v / UINT64_C(16) : 0);
  uint64_t lo = (UINT64_C(16) ? v % UINT64_C(16) : v);
  FinOperatesOnPairs::state s1 = set_reg(s, base, hi);
  return set_reg(std::move(s1), (base + UINT64_C(1)), lo);
}

FinOperatesOnPairs::state
FinOperatesOnPairs::execute_fin(const FinOperatesOnPairs::state &s,
                                uint64_t r) {
  return set_reg_pair(s, r,
                      ListDef::template nth<uint64_t>(
                          get_reg_pair(s, UINT64_C(0)), s.rom, UINT64_C(0)));
}
