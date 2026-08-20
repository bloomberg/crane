// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "object_model.h"

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
  // Test 1: point_test1 returns (1,3,2)
  {
    auto result = testtoST1_ext();
    ASSERT(result.first.first == 1);
    ASSERT(result.first.second == 3);
    ASSERT(result.second == 2);
    std::cout << "Test 1 (point_test1 works): (" << result.first.first << ", "
              << result.first.second << ", " << result.second << ")"
              << std::endl;
  }

  // Test 2: point_test2 returns (1, 10, 1,11)
  {
    auto result = testtoST2_ext();
    ASSERT(result.first.first.first == 1);
    ASSERT(result.first.first.second == 10);
    ASSERT(result.first.second == 1);
    ASSERT(result.second == 11);
    std::cout << "Test 2 (point_test2 works): (" << result.first.first.first
              << ", " << result.first.first.second << ", " << result.first.second
              << ", " << result.second << ")" << std::endl;
  }

  // Test 3: acc_test1 returns (100,150,false,150)
  {
    auto result = acc_test1_ext();
    ASSERT(result.first.first.first == 100);
    ASSERT(result.first.first.second == 150);
    ASSERT(result.first.second == false);
    ASSERT(result.second == 150);
    std::cout << "Test 3 (account1 works): (" << result.first.first.first
              << ", " << result.first.first.second << ", " << result.first.second
              << ", " << result.second << ")" << std::endl;
    
  }

  // Test 3: acc_test2 returns (100,true,250,0)
  {
    auto result = acc_test2_ext();
    ASSERT(result.first.first.first == 100);
    ASSERT(result.first.first.second == true);
    ASSERT(result.first.second == 250);
    ASSERT(result.second == 0);
    std::cout << "Test 4 (account2 works): (" << result.first.first.first
              << ", " << result.first.first.second << ", " << result.first.second
              << ", " << result.second << ")" << std::endl;
    
  }

  // Test 4: bank_acc_test1 returns (100,true,250,0)
  {
    auto result = bankacc_test1_ext();
    ASSERT(result.first.first.first == 100);
    ASSERT(result.first.first.second == true);
    ASSERT(result.first.second == 250);
    ASSERT(result.second == 0);
    std::cout << "Test 5 (bank_account1 works): (" << result.first.first.first
              << ", " << result.first.first.second << ", " << result.first.second
              << ", " << result.second << ")" << std::endl;
    
  }

  if (testStatus == 0) {
    std::cout << "\nAll object model tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}



