// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "st_fibonacci.h"

#include <iostream>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using nat_idx = StFibonacci::nat_idx;
using nat_stref = StFibonacci::nat_stref;

int main() {
  const uint64_t expected[] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55};
  for (uint64_t n = 0; n <= 10; ++n) {
    auto st = StFibonacci::fib_ST<nat_stref, nat_idx>(n);
    auto fun = StFibonacci::fib_fun(n);
    ASSERT(st == expected[n]);
    ASSERT(fun == expected[n]);
    std::cout << "fib_ST " << n << " = " << st << ", fib_fun " << n << " = "
              << fun << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll st_fibonacci tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
