// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "let_fix_intermediate_ref.h"

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
  // Test 1: sum_heads [[10;20]; [30]; []; [40;50]] = 10+30+0+40 = 80
  {
    ASSERT(LetFixIntermediateRef::test_heads == 80);
    std::cout << "Test 1 (sum_heads): PASSED" << std::endl;
  }

  // Test 2: zip_sum [1;2;3] [10;20;30] = 11+22+33 = 66
  {
    ASSERT(LetFixIntermediateRef::test_zip == 66);
    std::cout << "Test 2 (zip_sum): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll let_fix_intermediate_ref tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
