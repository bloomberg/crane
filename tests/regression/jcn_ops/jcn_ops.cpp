#include <jcn_ops.h>

#include <memory>
#include <type_traits>
#include <utility>

__attribute__((pure)) bool
JcnOps::jcn_condition(const std::shared_ptr<JcnOps::state> &s,
                      const unsigned int cond) {
  unsigned int c1 = (8u ? cond / 8u : 0);
  unsigned int c2 = ((4u ? cond / 4u : 0) % 2u);
  unsigned int c3 = ((2u ? cond / 2u : 0) % 2u);
  unsigned int c4 = (cond % 2u);
  bool base = ((s->acc == 0u && std::move(c2) == 1u) ||
               ((s->carry && std::move(c3) == 1u) ||
                (!(s->test_pin) && std::move(c4) == 1u)));
  if (std::move(c1) == 1u) {
    return !(std::move(base));
  } else {
    return std::move(base);
  }
}

__attribute__((pure)) unsigned int JcnOps::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

__attribute__((pure)) unsigned int
JcnOps::pc_inc2(const std::shared_ptr<JcnOps::state> &s) {
  return addr12_of_nat((s->pc + 2u));
}

__attribute__((pure)) unsigned int JcnOps::page_of(const unsigned int p) {
  return (256u ? p / 256u : 0);
}

__attribute__((pure)) unsigned int JcnOps::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

__attribute__((pure)) unsigned int
JcnOps::base_for_next2(const std::shared_ptr<JcnOps::state> &s) {
  return page_base(pc_inc2(s));
}

__attribute__((pure)) unsigned int
JcnOps::branch_target(const std::shared_ptr<JcnOps::state> &s,
                      const unsigned int cond, const unsigned int off) {
  if (jcn_condition(s, cond)) {
    return addr12_of_nat((base_for_next2(s) + off));
  } else {
    return addr12_of_nat((s->pc + 2u));
  }
}
