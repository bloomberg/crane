#include <isz_ops.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int IszOps::nibble_of_nat(const unsigned int n) {
  return (16u ? n % 16u : n);
}

__attribute__((pure)) unsigned int
IszOps::get_reg(const std::shared_ptr<IszOps::state> &s, const unsigned int r) {
  return s->regs->nth(r, 0u);
}

__attribute__((pure)) unsigned int
IszOps::cycles_isz(const std::shared_ptr<IszOps::state> &s,
                   const unsigned int r) {
  unsigned int new_val = nibble_of_nat((get_reg(s, r) + 1u));
  if (new_val == 0u) {
    return 8u;
  } else {
    return 16u;
  }
}

__attribute__((pure)) unsigned int
IszOps::isz_iterations(const unsigned int v) {
  if (v == 0u) {
    return 16u;
  } else {
    return (((16u - v) > 16u ? 0 : (16u - v)));
  }
}

__attribute__((pure)) bool
IszOps::isz_loops(const std::shared_ptr<IszOps::state> &s,
                  const unsigned int r) {
  return !(nibble_of_nat((get_reg(s, r) + 1u)) == 0u);
}

__attribute__((pure)) bool
IszOps::isz_terminates(const std::shared_ptr<IszOps::state> &s,
                       const unsigned int r) {
  return nibble_of_nat((get_reg(s, r) + 1u)) == 0u;
}
