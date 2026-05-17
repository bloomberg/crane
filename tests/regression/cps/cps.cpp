#include "cps.h"

uint64_t CPS::factorial(uint64_t n) {
  return fact_cps(n, [](uint64_t x) { return x; });
}

uint64_t CPS::fibonacci(uint64_t n) {
  return fib_cps(n, [](uint64_t x) { return x; });
}

uint64_t CPS::tree_sum(const CPS::tree &t) {
  return tree_sum_cps(t, [](uint64_t x) { return x; });
}

uint64_t CPS::list_sum(const List<uint64_t> &l) {
  return sum_cps(l, [](uint64_t x) { return x; });
}

uint64_t CPS::count_evens(const List<uint64_t> &l) {
  return partition_cps(Nat::even, l,
                       [](const List<uint64_t> &yes, const List<uint64_t> &) {
                         return yes.length();
                       });
}

bool Nat::even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      uint64_t n_ = n0 - 1;
      return Nat::even(n_);
    }
  }
}
