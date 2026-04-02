#include <preserves_all_pairs.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
PreservesAllPairs::get_reg(const std::shared_ptr<PreservesAllPairs::state> &s,
                           const unsigned int r) {
  return s->regs->nth(r, 0u);
}

__attribute__((pure)) unsigned int
PreservesAllPairs::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

__attribute__((pure)) unsigned int PreservesAllPairs::get_reg_pair(
    const std::shared_ptr<PreservesAllPairs::state> &s, const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<PreservesAllPairs::state>
PreservesAllPairs::execute_add(std::shared_ptr<PreservesAllPairs::state> s,
                               const unsigned int r) {
  return std::make_shared<PreservesAllPairs::state>(
      state{s->regs, nibble_of_nat((s->acc + get_reg(s, r)))});
}

std::shared_ptr<PreservesAllPairs::state>
PreservesAllPairs::execute_ld(std::shared_ptr<PreservesAllPairs::state> s,
                              const unsigned int r) {
  return std::make_shared<PreservesAllPairs::state>(
      state{s->regs, get_reg(s, r)});
}

std::shared_ptr<PreservesAllPairs::state>
PreservesAllPairs::execute_sub(std::shared_ptr<PreservesAllPairs::state> s,
                               const unsigned int r) {
  return std::make_shared<PreservesAllPairs::state>(state{
      s->regs, nibble_of_nat(((((s->acc + 16u) - get_reg(s, r)) > (s->acc + 16u)
                                   ? 0
                                   : ((s->acc + 16u) - get_reg(s, r)))))});
}
