#include <algorithm>
#include <any>
#include <cassert>
#include <decode_fin_wf_edge_0057.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int DecodeFinWfEdge0057::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int DecodeFinWfEdge0057::pc_inc2(
    const std::shared_ptr<DecodeFinWfEdge0057::state> &s) {
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
