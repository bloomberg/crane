#include <fin_operates_on_pairs.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
FinOperatesOnPairs::get_reg(const std::shared_ptr<FinOperatesOnPairs::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0u);
}

std::shared_ptr<FinOperatesOnPairs::state>
FinOperatesOnPairs::set_reg(std::shared_ptr<FinOperatesOnPairs::state> s,
                            const unsigned int r, const unsigned int v) {
  return std::make_shared<FinOperatesOnPairs::state>(
      state{update_nth<unsigned int>(r, (v % 16u), s->regs), s->rom});
}

__attribute__((pure)) unsigned int FinOperatesOnPairs::get_reg_pair(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<FinOperatesOnPairs::state> FinOperatesOnPairs::set_reg_pair(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r,
    const unsigned int v) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  unsigned int hi = (16u ? v / 16u : 0);
  unsigned int lo = (v % 16u);
  std::shared_ptr<FinOperatesOnPairs::state> s1 =
      set_reg(s, base, std::move(hi));
  return set_reg(std::move(s1), (std::move(base) + 1u), std::move(lo));
}

std::shared_ptr<FinOperatesOnPairs::state> FinOperatesOnPairs::execute_fin(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r) {
  return set_reg_pair(s, r, s->rom->nth(get_reg_pair(s, 0u), 0u));
}
