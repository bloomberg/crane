#include "preserves_all_pairs.h"

uint64_t PreservesAllPairs::get_reg(const PreservesAllPairs::state &s,
                                    uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

uint64_t PreservesAllPairs::nibble_of_nat(uint64_t n) {
  return (UINT64_C(16) ? n % UINT64_C(16) : n);
}

uint64_t PreservesAllPairs::get_reg_pair(const PreservesAllPairs::state &s,
                                         uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
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
  return state{s.regs, nibble_of_nat(
                           ((((s.acc + UINT64_C(16)) - get_reg(s, r)) >
                                     (s.acc + UINT64_C(16))
                                 ? 0
                                 : ((s.acc + UINT64_C(16)) - get_reg(s, r)))))};
}
