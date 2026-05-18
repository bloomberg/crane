// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "let_fix_nested_clone.h"

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
  // Test 1: sum_nested [[1;2]; [3]; [4;5;6]] = 21
  {
    ASSERT(LetFixNestedClone::test_sum == 21);
    std::cout << "Test 1 (sum_nested): PASSED" << std::endl;
  }

  // Test 2: count_nested [[1;2]; [3]; [4;5;6]] = 6
  {
    ASSERT(LetFixNestedClone::test_count == 6);
    std::cout << "Test 2 (count_nested): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll let_fix_nested_clone tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
