// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for any_cast<crane::obj> in nested pair destructuring.
//
// symbols_semty erases to crane::obj, and SemVal (axiom type) also maps
// to crane::obj.  The compiler must elide the redundant any_cast<crane::obj>
// when destructuring bound variables whose declared type resolves to
// crane::obj.

#include "any_cast_nested_pair.h"

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
  // Build the pair<any, any> representation that apply_pred expects.
  // mkSemVal is inlined as crane::obj(n), so we construct directly.
  crane::obj inner_pair =
      std::make_pair(crane::obj(uint64_t(20)), crane::obj(std::monostate{}));
  crane::obj input =
      std::make_pair(crane::obj(uint64_t(10)), inner_pair);

  uint64_t result = AnyCastNestedPair::apply_pred(input);
  ASSERT(result == 30);
  if (testStatus == 0) {
    std::cout << "apply_pred returned " << result << " -- correct\n";
  }

  return testStatus;
}
