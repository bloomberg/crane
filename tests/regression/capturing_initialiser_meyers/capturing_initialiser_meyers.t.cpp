// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// A functor's value initialised by an expression holding a capturing lambda:
// written as a function-local static, its initialiser invoked in place.
#include <capturing_initialiser_meyers.h>

#include <iostream>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // (1 + 5) + (2 + 5) + (3 + 5), the base being 4.
  ASSERT(CapturingInitialiserMeyers::shifted_sum_four == 21);
  ASSERT(CapturingInitialiserMeyers::SumsFour::shifted_sum() == 21);
  return testStatus;
}
