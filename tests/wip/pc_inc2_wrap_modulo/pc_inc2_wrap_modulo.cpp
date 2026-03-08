#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <pc_inc2_wrap_modulo.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int PcInc2WrapModulo::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int
PcInc2WrapModulo::pc_inc2(const std::shared_ptr<PcInc2WrapModulo::state> &s) {
  return addr12_of_nat((s->pc + 2u));
}

unsigned int Nat::pow(const unsigned int n, const unsigned int m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
}
