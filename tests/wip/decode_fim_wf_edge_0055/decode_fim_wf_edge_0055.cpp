#include <algorithm>
#include <any>
#include <cassert>
#include <decode_fim_wf_edge_0055.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int DecodeFimWfEdge0055::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int DecodeFimWfEdge0055::pc_inc1(
    const std::shared_ptr<DecodeFimWfEdge0055::state> &s) {
  return addr12_of_nat((s->pc + 1u));
}

unsigned int Nat::pow(const unsigned int n, const unsigned int m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
}
