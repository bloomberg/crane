// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "ind_param.h"

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
  // Test 1: test_size_single - should be 1 (single element container)
  {
    unsigned int result = IndParam::test_size_single;
    ASSERT(result == 1);
    std::cout << "Test 1 (single element size): " << result << " (expected 1): PASSED" << std::endl;
  }

  // Test 2: test_size_pair - should be 2 (pair container)
  {
    unsigned int result = IndParam::test_size_pair;
    ASSERT(result == 2);
    std::cout << "Test 2 (pair size): " << result << " (expected 2): PASSED" << std::endl;
  }

  // Test 3: test_error - should be 0 (error result has no container)
  {
    unsigned int result = IndParam::test_error;
    ASSERT(result == 0);
    std::cout << "Test 3 (error result size): " << result << " (expected 0): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll parameterized inductive tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
