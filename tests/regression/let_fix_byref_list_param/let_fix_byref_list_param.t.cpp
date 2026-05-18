// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "let_fix_byref_list_param.h"

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
  // Test 1: count_elements [1;2;3;4;5] = 5
  {
    ASSERT(LetFixByrefListParam::test_count == 5);
    std::cout << "Test 1 (count_elements): PASSED" << std::endl;
  }

  // Test 2: sum_with_acc [10;20;30] = 60
  {
    ASSERT(LetFixByrefListParam::test_sum == 60);
    std::cout << "Test 2 (sum_with_acc): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll let_fix_byref_list_param tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
