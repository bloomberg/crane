#include "preserves_all_pairs.h"

uint64_t PreservesAllPairs::get_reg(const PreservesAllPairs::state &s,
                                    uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

uint64_t PreservesAllPairs::nibble_of_nat(uint64_t n) {
  return (n % UINT64_C(16));
}

uint64_t PreservesAllPairs::get_reg_pair(const PreservesAllPairs::state &s,
                                         uint64_t r) {
  auto &&_once1 = (r % UINT64_C(2));
  uint64_t base = (((r - _once1) > r ? 0 : (r - _once1)));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

PreservesAllPairs::state
PreservesAllPairs::execute_add(const PreservesAllPairs::state &s, uint64_t r) {
  return state{s.regs, nibble_of_nat((s.acc + get_reg(s, r)))};
}

PreservesAllPairs::state
PreservesAllPairs::execute_ld(const PreservesAllPairs::state &s, uint64_t r) {
  return state{s.regs, get_reg(s, r)};
}

PreservesAllPairs::state
PreservesAllPairs::execute_sub(const PreservesAllPairs::state &s, uint64_t r) {
  auto &&_once1 = (s.acc + UINT64_C(16));
  auto &&_once2 = get_reg(s, r);
  return state{
      s.regs,
      nibble_of_nat((((_once1 - _once2) > _once1 ? 0 : (_once1 - _once2))))};
}
