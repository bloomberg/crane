// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "nested_mod.h"

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
  // Test 1: test_area - circle with radius 5, area = 5*5*3 = 75
  {
    unsigned int result = test_area;
    ASSERT(result == 75);
    std::cout << "Test 1 (circle area): " << result << " (expected 75): PASSED" << std::endl;
  }

  // Test 2: test_combined - red circle (area 75 + 100 = 175)
  {
    unsigned int result = test_combined;
    ASSERT(result == 175);
    std::cout << "Test 2 (red colored shape): " << result << " (expected 175): PASSED" << std::endl;
  }

  // Test 3: test_color - Red has code 1
  {
    unsigned int result = test_color;
    ASSERT(result == 1);
    std::cout << "Test 3 (color code): " << result << " (expected 1): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll nested module tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
