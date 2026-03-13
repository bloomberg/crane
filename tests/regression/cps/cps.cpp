#include <cps.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int CPS::factorial(const unsigned int n) {
  return fact_cps(n, [](unsigned int x) { return x; });
}

__attribute__((pure)) unsigned int CPS::fibonacci(const unsigned int n) {
  return fib_cps(n, [](unsigned int x) { return x; });
}

__attribute__((pure)) unsigned int
CPS::tree_sum(const std::shared_ptr<CPS::tree> &t) {
  return tree_sum_cps(t, [](unsigned int x) { return x; });
}

__attribute__((pure)) unsigned int
CPS::list_sum(const std::shared_ptr<List<unsigned int>> &l) {
  return sum_cps(l, [](unsigned int x) { return x; });
}

__attribute__((pure)) unsigned int
CPS::count_evens(const std::shared_ptr<List<unsigned int>> &l) {
  return partition_cps(
      Nat::even, l,
      [](std::shared_ptr<List<unsigned int>> yes,
         std::shared_ptr<List<unsigned int>> _x) { return yes->length(); });
}

__attribute__((pure)) bool Nat::even(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      unsigned int n_ = n0 - 1;
      return Nat::even(n_);
    }
  }
}
