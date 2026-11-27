// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <st_readable_forms.h>

#include <iostream>

namespace {
int failures = 0;
void check(bool ok, const char *what) {
  if (!ok) {
    std::cout << "FAILED: " << what << std::endl;
    ++failures;
  }
}
} // namespace

int main() {
  using M = StReadableForms;
  check(M::pair_parts == 9, "pair_parts = 3 + 6");
  check(M::fib_step(10) == 55, "fib_step 10 = 55");
  check(M::fib_step(1) == 1, "fib_step 1 = 1");
  check(M::sum_with == 19, "sum_with = 3 + 3 + 10 + 3");
  check(M::count_back == 15, "count_back = 1 + 2 + 3 + 4 + 5");
  check(M::unused_param == 5, "unused_param = 4 + 1");
  if (failures == 0) {
    std::cout << "st_readable_forms: all tests passed" << std::endl;
  }
  return failures;
}
