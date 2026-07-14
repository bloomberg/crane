#include "stmonad.h"

uint64_t STMonadTests::fib_fun(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m0 = n - 1;
    if (m0 <= 0) {
      return UINT64_C(1);
    } else {
      uint64_t m = m0 - 1;
      return (fib_fun(m0) + fib_fun(m));
    }
  }
}

List<uint64_t> STMonadTests::quicksort_fun(const List<uint64_t> &x) {
  return STMonadExamples::quicksort_fun_functional(
      x, [](const List<uint64_t> &y) { return quicksort_fun(y); });
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
