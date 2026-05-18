#include "register_pair_ops.h"

uint64_t RegisterPairOps::get_reg(const RegisterPairOps::state &s, uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

RegisterPairOps::state RegisterPairOps::set_reg(const RegisterPairOps::state &s,
                                                uint64_t r, uint64_t v) {
  return state{
      update_nth<uint64_t>(r, (UINT64_C(16) ? v % UINT64_C(16) : v), s.regs)};
}

uint64_t RegisterPairOps::get_reg_pair(const RegisterPairOps::state &s,
                                       uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

RegisterPairOps::state
RegisterPairOps::set_reg_pair(const RegisterPairOps::state &s, uint64_t r,
                              uint64_t v) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  uint64_t hi = (UINT64_C(16) ? v / UINT64_C(16) : 0);
  uint64_t lo = (UINT64_C(16) ? v % UINT64_C(16) : v);
  RegisterPairOps::state s1 = set_reg(s, base, hi);
  return set_reg(std::move(s1), (base + UINT64_C(1)), lo);
}

uint64_t RegisterPairOps::pair_base(uint64_t r) {
  return (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
               ? 0
               : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
}

uint64_t RegisterPairOps::pair_index(uint64_t r) {
  return (UINT64_C(2) ? r / UINT64_C(2) : 0);
}

bool RegisterPairOps::pair_property(uint64_t r) {
  uint64_t p = pair_index(r);
  return (p < UINT64_C(8) &&
          (r == (UINT64_C(2) * p) || r == ((UINT64_C(2) * p) + UINT64_C(1))));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
