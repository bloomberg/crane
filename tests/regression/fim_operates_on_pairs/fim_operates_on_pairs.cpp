#include <fim_operates_on_pairs.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
FimOperatesOnPairs::get_reg(const std::shared_ptr<FimOperatesOnPairs::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0u);
}

std::shared_ptr<FimOperatesOnPairs::state>
FimOperatesOnPairs::set_reg(const std::shared_ptr<FimOperatesOnPairs::state> &s,
                            const unsigned int r, const unsigned int v) {
  return std::make_shared<FimOperatesOnPairs::state>(
      state{update_nth<unsigned int>(r, (16u ? v % 16u : v), s->regs)});
}

__attribute__((pure)) unsigned int FimOperatesOnPairs::get_reg_pair(
    const std::shared_ptr<FimOperatesOnPairs::state> &s, const unsigned int r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<FimOperatesOnPairs::state> FimOperatesOnPairs::set_reg_pair(
    const std::shared_ptr<FimOperatesOnPairs::state> &s, const unsigned int r,
    const unsigned int v) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  unsigned int hi = (16u ? v / 16u : 0);
  unsigned int lo = (16u ? v % 16u : v);
  std::shared_ptr<FimOperatesOnPairs::state> s1 = set_reg(s, base, hi);
  return set_reg(std::move(s1), (base + 1u), lo);
}

std::shared_ptr<FimOperatesOnPairs::state> FimOperatesOnPairs::execute_fim(
    const std::shared_ptr<FimOperatesOnPairs::state> &_x0,
    const unsigned int _x1, const unsigned int _x2) {
  return set_reg_pair(_x0, _x1, _x2);
}
