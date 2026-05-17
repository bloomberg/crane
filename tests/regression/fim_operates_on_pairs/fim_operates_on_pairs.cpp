#include "fim_operates_on_pairs.h"

uint64_t FimOperatesOnPairs::get_reg(const FimOperatesOnPairs::state &s,
                                     uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

FimOperatesOnPairs::state
FimOperatesOnPairs::set_reg(const FimOperatesOnPairs::state &s, uint64_t r,
                            uint64_t v) {
  return state{
      update_nth<uint64_t>(r, (UINT64_C(16) ? v % UINT64_C(16) : v), s.regs)};
}

uint64_t FimOperatesOnPairs::get_reg_pair(const FimOperatesOnPairs::state &s,
                                          uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

FimOperatesOnPairs::state
FimOperatesOnPairs::set_reg_pair(const FimOperatesOnPairs::state &s, uint64_t r,
                                 uint64_t v) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  uint64_t hi = (UINT64_C(16) ? v / UINT64_C(16) : 0);
  uint64_t lo = (UINT64_C(16) ? v % UINT64_C(16) : v);
  FimOperatesOnPairs::state s1 = set_reg(s, base, hi);
  return set_reg(std::move(s1), (base + UINT64_C(1)), lo);
}

FimOperatesOnPairs::state
FimOperatesOnPairs::execute_fim(const FimOperatesOnPairs::state &_x0,
                                uint64_t _x1, uint64_t _x2) {
  return set_reg_pair(_x0, _x1, _x2);
}
