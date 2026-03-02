// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "canon_struct.h"

#include <iostream>

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
  // Test 1: test_nat — same 3 5 = false
  {
    ASSERT(CanonStruct::test_nat == false);
    std::cout << "Test 1 (test_nat): PASSED" << std::endl;
  }

  // Test 2: test_bool — same true false = false
  {
    ASSERT(CanonStruct::test_bool == false);
    std::cout << "Test 2 (test_bool): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll canonical structure tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
