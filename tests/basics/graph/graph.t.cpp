// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "graph.h"

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
  // Test that the code compiles and basic functionality works
  ASSERT(test_int_eq == true);

  // Test that test_eq works with explicit type class instance
  bool result = test_eq<IntEq, int>(5, 5);
  ASSERT(result == true);

  bool result2 = test_eq<IntEq, int>(5, 6);
  ASSERT(result2 == false);

  std::cout << "All graph tests passed!" << std::endl;

  return testStatus;
}
