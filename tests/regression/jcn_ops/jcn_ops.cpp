#include "jcn_ops.h"

bool JcnOps::jcn_condition(const JcnOps::state &s, uint64_t cond) {
  uint64_t c1 = (UINT64_C(8) ? cond / UINT64_C(8) : 0);
  uint64_t c2 =
      (UINT64_C(2) ? (UINT64_C(4) ? cond / UINT64_C(4) : 0) % UINT64_C(2)
                   : (UINT64_C(4) ? cond / UINT64_C(4) : 0));
  uint64_t c3 =
      (UINT64_C(2) ? (UINT64_C(2) ? cond / UINT64_C(2) : 0) % UINT64_C(2)
                   : (UINT64_C(2) ? cond / UINT64_C(2) : 0));
  uint64_t c4 = (UINT64_C(2) ? cond % UINT64_C(2) : cond);
  bool base = ((s.acc == UINT64_C(0) && c2 == UINT64_C(1)) ||
               ((s.carry && c3 == UINT64_C(1)) ||
                (!(s.test_pin) && c4 == UINT64_C(1))));
  if (c1 == UINT64_C(1)) {
    return !(base);
  } else {
    return base;
  }
}

uint64_t JcnOps::addr12_of_nat(uint64_t n) {
  return (UINT64_C(4096) ? n % UINT64_C(4096) : n);
}

uint64_t JcnOps::pc_inc2(const JcnOps::state &s) {
  return addr12_of_nat((s.pc + UINT64_C(2)));
}

uint64_t JcnOps::page_of(uint64_t p) {
  return (UINT64_C(256) ? p / UINT64_C(256) : 0);
}

uint64_t JcnOps::page_base(uint64_t p) { return (page_of(p) * UINT64_C(256)); }

uint64_t JcnOps::base_for_next2(const JcnOps::state &s) {
  return page_base(pc_inc2(s));
}

uint64_t JcnOps::branch_target(const JcnOps::state &s, uint64_t cond,
                               uint64_t off) {
  if (jcn_condition(s, cond)) {
    return addr12_of_nat((base_for_next2(s) + off));
  } else {
    return addr12_of_nat((s.pc + UINT64_C(2)));
  }
}
