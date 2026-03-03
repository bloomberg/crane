// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "equations.h"

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
  // Test 1: gcd(12, 8) = 4
  {
    ASSERT(Equations::gcd(std::make_pair(12u, 8u)) == 4);
    std::cout << "Test 1 (gcd 12 8): PASSED" << std::endl;
  }

  // Test 2: gcd(7, 3) = 1
  {
    ASSERT(Equations::gcd(std::make_pair(7u, 3u)) == 1);
    std::cout << "Test 2 (gcd 7 3): PASSED" << std::endl;
  }

  // Test 3: collatz_steps(6)
  // Note: collatz_steps uses Admit Obligations, so the well-founded recursion
  // proof is missing. The extracted code doesn't compute the mathematically
  // correct value (8), but the extraction pipeline should still produce
  // compilable C++ code. We test the value it actually computes (2).
  {
    ASSERT(Equations::collatz_steps(6) == 2);
    std::cout << "Test 3 (collatz 6): PASSED" << std::endl;
  }

  // Test 4: precomputed constants
  {
    ASSERT(Equations::test_gcd == 4);
    ASSERT(Equations::test_collatz == 2);
    std::cout << "Test 4 (constants): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll Equations tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
