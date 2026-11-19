// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "st_quicksort.h"

#include <iostream>
#include <string>

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

int main() {
  const List<uint64_t> lst = List<uint64_t>::cons(
      4, List<uint64_t>::cons(
             1, List<uint64_t>::cons(2, List<uint64_t>::nil())));

  {
    auto result = StQuicksort::quicksort_fun(lst);
    ASSERT(result.length() == 3);
    ASSERT(StQuicksort::nth(0, result, 0) == 1);
    ASSERT(StQuicksort::nth(1, result, 0) == 2);
    ASSERT(StQuicksort::nth(2, result, 0) == 4);
    std::cout << "quicksort_fun [4; 1; 2]: [" << StQuicksort::nth(0, result, 0)
              << ", " << StQuicksort::nth(1, result, 0) << ", "
              << StQuicksort::nth(2, result, 0) << "]" << std::endl;
  }

  {
    auto result = StQuicksort::quicksort_ST_mine(lst);
    ASSERT(result.length() == 3);
    ASSERT(StQuicksort::nth(0, result, 0) == 1);
    ASSERT(StQuicksort::nth(1, result, 0) == 2);
    ASSERT(StQuicksort::nth(2, result, 0) == 4);
    std::cout << "quicksort_ST_mine [4; 1; 2]: ["
              << StQuicksort::nth(0, result, 0) << ", "
              << StQuicksort::nth(1, result, 0) << ", "
              << StQuicksort::nth(2, result, 0) << "]" << std::endl;
  }

  {
    const std::string expected =
        "[ 4, 51, 126, 127, 2412, 5981, 10645, 74879, 212498, 2749812,  ]";
    auto st = StQuicksort::test_quicksort_ST();
    auto fun = StQuicksort::test_quicksort_fun();
    ASSERT(st == expected);
    ASSERT(fun == expected);
    std::cout << "test_quicksort_ST: " << st << std::endl;
    std::cout << "test_quicksort_fun: " << fun << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll st_quicksort tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
