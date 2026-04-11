#include <register_pair_ops.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
RegisterPairOps::get_reg(const std::shared_ptr<RegisterPairOps::state> &s,
                         const unsigned int r) {
  return s->regs->nth(r, 0u);
}

std::shared_ptr<RegisterPairOps::state>
RegisterPairOps::set_reg(std::shared_ptr<RegisterPairOps::state> s,
                         const unsigned int r, const unsigned int v) {
  return std::make_shared<RegisterPairOps::state>(
      state{update_nth<unsigned int>(r, (16u ? v % 16u : v), s->regs)});
}

__attribute__((pure)) unsigned int
RegisterPairOps::get_reg_pair(const std::shared_ptr<RegisterPairOps::state> &s,
                              const unsigned int r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<RegisterPairOps::state>
RegisterPairOps::set_reg_pair(const std::shared_ptr<RegisterPairOps::state> &s,
                              const unsigned int r, const unsigned int v) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  unsigned int hi = (16u ? v / 16u : 0);
  unsigned int lo = (16u ? v % 16u : v);
  std::shared_ptr<RegisterPairOps::state> s1 = set_reg(s, base, hi);
  return set_reg(std::move(s1), (base + 1u), lo);
}

__attribute__((pure)) unsigned int
RegisterPairOps::pair_base(const unsigned int r) {
  return (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
}

__attribute__((pure)) unsigned int
RegisterPairOps::pair_index(const unsigned int r) {
  return (2u ? r / 2u : 0);
}

__attribute__((pure)) bool
RegisterPairOps::pair_property(const unsigned int r) {
  unsigned int p = pair_index(r);
  return (p < 8u && (r == (2u * p) || r == ((2u * p) + 1u)));
}

std::shared_ptr<List<unsigned int>> ListDef::seq(const unsigned int start,
                                                 const unsigned int len) {
  if (len <= 0) {
    return List<unsigned int>::nil();
  } else {
    unsigned int len0 = len - 1;
    return List<unsigned int>::cons(start, ListDef::seq((start + 1), len0));
  }
}
