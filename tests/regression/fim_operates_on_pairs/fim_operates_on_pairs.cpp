#include <fim_operates_on_pairs.h>

__attribute__((pure)) unsigned int
FimOperatesOnPairs::get_reg(const FimOperatesOnPairs::state &s,
                            const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.regs, 0u);
}

__attribute__((pure)) FimOperatesOnPairs::state
FimOperatesOnPairs::set_reg(const FimOperatesOnPairs::state &s,
                            const unsigned int &r, const unsigned int &v) {
  return state{update_nth<unsigned int>(r, (16u ? v % 16u : v), s.regs)};
}

__attribute__((pure)) unsigned int
FimOperatesOnPairs::get_reg_pair(const FimOperatesOnPairs::state &s,
                                 const unsigned int &r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

__attribute__((pure)) FimOperatesOnPairs::state
FimOperatesOnPairs::set_reg_pair(const FimOperatesOnPairs::state &s,
                                 const unsigned int &r, const unsigned int &v) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  unsigned int hi = (16u ? v / 16u : 0);
  unsigned int lo = (16u ? v % 16u : v);
  FimOperatesOnPairs::state s1 = set_reg(s, base, hi);
  return set_reg(std::move(s1), (base + 1u), lo);
}

__attribute__((pure)) FimOperatesOnPairs::state
FimOperatesOnPairs::execute_fim(const FimOperatesOnPairs::state &_x0,
                                const unsigned int &_x1,
                                const unsigned int &_x2) {
  return set_reg_pair(_x0, _x1, _x2);
}
