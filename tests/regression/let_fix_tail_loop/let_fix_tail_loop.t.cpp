// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "let_fix_tail_loop.h"

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
  // Test 1: sum_list [1;2;3;4;5] = 15
  {
    ASSERT(LetFixTailLoop::test_sum == 15);
    std::cout << "Test 1 (sum_list): PASSED" << std::endl;
  }

  // Test 2: length_list [10;20;30;40] = 4
  {
    ASSERT(LetFixTailLoop::test_len == 4);
    std::cout << "Test 2 (length_list): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll let_fix_tail_loop tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
