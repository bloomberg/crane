#include <addr12_of_nat_add_edge_0025.h>
#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int Addr12OfNatAddEdge0025::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int Addr12OfNatAddEdge0025::pc_inc2(
    const std::shared_ptr<Addr12OfNatAddEdge0025::state> &s) {
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
