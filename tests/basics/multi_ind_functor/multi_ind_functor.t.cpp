// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "multi_ind_functor.h"

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
  // Test 1: test_is_nothing - empty_maybe is Nothing, so should be true
  {
    bool result = test_is_nothing;
    ASSERT(result == true);
    std::cout << "Test 1 (is_nothing): " << (result ? "true" : "false") << " (expected true): PASSED" << std::endl;
  }

  // Test 2: test_list_len - sample_list has 2 elements (Just 42, Nothing)
  {
    unsigned int result = test_list_len;
    ASSERT(result == 2);
    std::cout << "Test 2 (list length): " << result << " (expected 2): PASSED" << std::endl;
  }

  // Test 3: test_tree_size - sample_tree is Node with 2 children
  {
    unsigned int result = test_tree_size;
    ASSERT(result == 2);
    std::cout << "Test 3 (tree size): " << result << " (expected 2): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll multi-inductive functor tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
