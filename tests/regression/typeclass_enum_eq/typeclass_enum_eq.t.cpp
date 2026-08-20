// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "typeclass_enum_eq.h"

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

} // close unnamed namespace

#define ASSERT(X)                                                              \
  {                                                                            \
    aSsErT(!(X), #X, __LINE__);                                                \
  }

int main() {
  using M = TypeclassEnumEq;
  using Color = M::Color;

  // The instance satisfies the concept, and dispatch is static.  The calls
  // are hoisted out of ASSERT because the comma in the template argument
  // list would otherwise be read as a macro argument separator.
  const bool sameRed = M::is_equal<M::ColorEq, Color>(Color::RED, Color::RED);
  const bool redBlue = M::is_equal<M::ColorEq, Color>(Color::RED, Color::BLUE);
  const bool sameGreen =
      M::is_equal<M::ColorEq, Color>(Color::GREEN, Color::GREEN);
  const bool greenBlue =
      M::is_equal<M::ColorEq, Color>(Color::GREEN, Color::BLUE);

  ASSERT(sameRed);
  ASSERT(!redBlue);
  ASSERT(sameGreen);
  ASSERT(!greenBlue);

  // The extracted constants agree.
  ASSERT(M::test_same);
  ASSERT(!M::test_diff);

  if (testStatus > 0) {
    std::cout << "Error, non-zero test status = " << testStatus << "."
              << std::endl;
  }
  return testStatus;
}
