// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "prim_proj.h"

#include <iostream>

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
  // Test 1: origin is (0, 0)
  {
    ASSERT(PrimProj::origin.px == 0);
    ASSERT(PrimProj::origin.py == 0);
    std::cout << "Test 1 (origin): PASSED" << std::endl;
  }

  // Test 3: translate
  {
    PrimProj::point p{10, 20};
    auto moved = PrimProj::translate(5, 3, p);
    ASSERT(moved.px == 15);
    ASSERT(moved.py == 23);
    std::cout << "Test 3 (translate): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll primitive projection tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
