#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <init_state_edge_0033.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int InitStateEdge0033::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int Nat::pow(const unsigned int n, const unsigned int m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
}
