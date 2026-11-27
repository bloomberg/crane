// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "st_arrays.h"

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

int main() {
  {
    auto result = STArrays::array_simp_fixed_init();
    ASSERT(result == 5);
    std::cout << "array_simp_fixed_init: " << result << std::endl;
  }

  {
    auto result = STArrays::array_simp_list();
    ASSERT(result.first.first == 5);
    ASSERT(result.first.second == 4);
    ASSERT(STArrays::nth(0, result.second, 0) == 5);
    ASSERT(STArrays::nth(1, result.second, 0) == 4);
    ASSERT(STArrays::nth(2, result.second, 0) == 3);
    ASSERT(STArrays::nth(3, result.second, 0) == 2);
    std::cout << "array_simp_list: " << result.first.first << ", "
              << result.first.second << ", [" << STArrays::nth(0, result.second, 0)
              << ", " << STArrays::nth(1, result.second, 0) << ", "
              << STArrays::nth(2, result.second, 0) << ", "
              << STArrays::nth(3, result.second, 0) << "]" << std::endl;
  }

  {
    List<uint64_t> lst = List<uint64_t>::cons(
        1, List<uint64_t>::cons(
               2, List<uint64_t>::cons(3, List<uint64_t>::nil())));
    auto result = STArrays::swap_first_and_last_list(lst);
    ASSERT(result.length() == 3);
    ASSERT(STArrays::nth(0, result, 0) == 3);
    ASSERT(STArrays::nth(1, result, 0) == 2);
    ASSERT(STArrays::nth(2, result, 0) == 1);
    std::cout << "swap_first_and_last_list [1; 2; 3]: ["
              << STArrays::nth(0, result, 0) << ", "
              << STArrays::nth(1, result, 0) << ", "
              << STArrays::nth(2, result, 0) << "]" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll st_arrays tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
