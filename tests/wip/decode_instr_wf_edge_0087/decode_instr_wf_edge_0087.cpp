#include <algorithm>
#include <any>
#include <cassert>
#include <decode_instr_wf_edge_0087.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int DecodeInstrWfEdge0087::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int DecodeInstrWfEdge0087::pc_inc1(
    const std::shared_ptr<DecodeInstrWfEdge0087::state> &s) {
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
