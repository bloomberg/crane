// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "stmonad.h"


#include <iostream>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

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
  // Test 1: newAndReadBoth returns (5, 6)
  {
    auto result = newAndReadBoth<STMonadTests::nat_idx, STMonadTests::nat_stref, void>();
    ASSERT(result.first == 5);
    ASSERT(result.second == 6);
    std::cout << "Test 1 (newAndReadBoth): (" << result.first << ", "
              << result.second << ") PASSED" << std::endl;
  }

  // Test 2: tree_simp returns 5
  {
    auto result = tree_simp<STMonadTests::nat_idx, STMonadTests::nat_stref, void>();
    ASSERT(result == 5);
    std::cout << "Test 2 (tree_simp): " << result << " PASSED"
              << std::endl;
  }

  // Test 3: tree_simp_another returns 6
  {
    auto result = tree_simp_another<STMonadTests::nat_stref, STMonadTests::nat_idx, void>();
    ASSERT(result == 6);
    std::cout << "Test 3 (tree_simp_another): " << result
              << " PASSED" << std::endl;
  }

  {
    auto result = array_simp_fixed_init<STMonadTests::nat_stref, STMonadTests::nat_idx, void>();
    ASSERT(result == 5);
    std::cout << "Test 4 (array_simp_fixed_init): " << result
              << " PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll stmonad tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}

