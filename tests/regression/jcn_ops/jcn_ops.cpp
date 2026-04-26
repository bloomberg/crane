#include <jcn_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

__attribute__((pure)) bool JcnOps::jcn_condition(const JcnOps::state &s,
                                                 const unsigned int &cond) {
  unsigned int c1 = (8u ? cond / 8u : 0);
  unsigned int c2 = (2u ? (4u ? cond / 4u : 0) % 2u : (4u ? cond / 4u : 0));
  unsigned int c3 = (2u ? (2u ? cond / 2u : 0) % 2u : (2u ? cond / 2u : 0));
  unsigned int c4 = (2u ? cond % 2u : cond);
  bool base = ((s.acc == 0u && c2 == 1u) ||
               ((s.carry && c3 == 1u) || (!(s.test_pin) && c4 == 1u)));
  if (c1 == 1u) {
    return !(base);
  } else {
    return base;
  }
}

__attribute__((pure)) unsigned int
JcnOps::addr12_of_nat(const unsigned int &n) {
  return (4096u ? n % 4096u : n);
}

__attribute__((pure)) unsigned int JcnOps::pc_inc2(const JcnOps::state &s) {
  return addr12_of_nat((s.pc + 2u));
}

__attribute__((pure)) unsigned int JcnOps::page_of(const unsigned int &p) {
  return (256u ? p / 256u : 0);
}

__attribute__((pure)) unsigned int JcnOps::page_base(const unsigned int &p) {
  return (page_of(p) * 256u);
}

__attribute__((pure)) unsigned int
JcnOps::base_for_next2(const JcnOps::state &s) {
  return page_base(pc_inc2(s));
}

__attribute__((pure)) unsigned int
JcnOps::branch_target(const JcnOps::state &s, const unsigned int &cond,
                      const unsigned int &off) {
  if (jcn_condition(s, cond)) {
    return addr12_of_nat((base_for_next2(s) + off));
  } else {
    return addr12_of_nat((s.pc + 2u));
  }
}
