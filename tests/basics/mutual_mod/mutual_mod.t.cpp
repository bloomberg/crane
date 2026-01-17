// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "mutual_mod.h"

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main() {
  // Test 1: test_even_len - even list [2, 1] has length 2
  {
    unsigned int result = test_even_len;
    ASSERT(result == 2);
    std::cout << "Test 1 (even list length): " << result << " (expected 2): PASSED" << std::endl;
  }

  // Test 2: test_odd_len - odd list [3, 2, 1] has length 3
  {
    unsigned int result = test_odd_len;
    ASSERT(result == 3);
    std::cout << "Test 2 (odd list length): " << result << " (expected 3): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll mutual inductive module tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
