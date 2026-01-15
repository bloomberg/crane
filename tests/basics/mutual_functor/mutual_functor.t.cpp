// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "mutual_functor.h"

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
  // Test 1: test_tree_size - sample_tree = Node 0 [Leaf 1, Leaf 2]
  //         size = 1 (for Node) + 1 (Leaf 1) + 1 (Leaf 2) = 3
  {
    unsigned int result = test_tree_size;
    ASSERT(result == 3);
    std::cout << "Test 1 (tree size): " << result << " (expected 3): PASSED" << std::endl;
  }

  // Test 2: test_forest_size - small_forest = [Leaf 1, Leaf 2]
  //         size = 1 + 1 = 2
  {
    unsigned int result = test_forest_size;
    ASSERT(result == 2);
    std::cout << "Test 2 (forest size): " << result << " (expected 2): PASSED" << std::endl;
  }

  // Test 3: test_tree_sum - sample_tree = Node 0 [Leaf 1, Leaf 2]
  //         sum = 0 + 1 + 2 = 3
  {
    unsigned int result = test_tree_sum;
    ASSERT(result == 3);
    std::cout << "Test 3 (tree sum): " << result << " (expected 3): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll mutual functor tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
