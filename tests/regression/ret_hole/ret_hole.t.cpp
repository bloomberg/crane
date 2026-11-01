// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "ret_hole.h"

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
  ASSERT(RetHole::quadruple(0) == 0);
  ASSERT(RetHole::quadruple(3) == 12);

  if (testStatus == 0) {
    std::cout << "All ret_hole tests passed!" << std::endl;
  } else {
    std::cout << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
