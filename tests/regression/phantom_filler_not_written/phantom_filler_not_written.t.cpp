// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <phantom_filler_not_written.h>

#include <iostream>

int main() {
  auto xs = List<uint64_t>::cons(
      3, List<uint64_t>::cons(4, List<uint64_t>::cons(5, List<uint64_t>::nil())));
  int failures = 0;
  auto sum = PhantomFillerNotWritten::sum_list(xs);
  if (sum != 12) {
    std::cout << "sum_list: expected 12, got " << sum << std::endl;
    ++failures;
  }
  if (failures == 0) {
    std::cout << "phantom_filler_not_written: all tests passed" << std::endl;
  }
  return failures;
}
