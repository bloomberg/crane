// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for missing any_cast when returning a type-erased sigT
// payload as a concrete template type.
//
// EXPECTED: This test currently FAILS TO COMPILE because the generated
// extract_a<T1> function does "return a1;" where a1 is std::any but
// the function return type is T1.  The fix should insert
// any_cast<T1>(a1) in the S branch.
//
// The O branch (nested pair destructuring) demonstrates the
// apply_fixc_to_nested path and correctly generates any_cast<T1>(a0).
// The S branch is the failing case — it returns the raw sigT payload
// (std::any) without casting to the return type T1.
//
// Once the bug is fixed, this test should pass at runtime:
// test_extract(42) calls extract_a<uint64_t> with the O branch,
// returning 42 via the correct nested pair path.

#include "any_cast_nested.h"

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
  // test_extract(42) constructs sigT(0, pair(10, pair(20, 42)))
  // and extracts the innermost value (42) via nested pair matching.
  uint64_t result = AnyCastNested::test_extract(42);
  ASSERT(result == 42);

  uint64_t result2 = AnyCastNested::test_extract(99);
  ASSERT(result2 == 99);

  if (testStatus == 0) {
    std::cout << "test_extract(42) = " << result << " -- correct\n";
    std::cout << "test_extract(99) = " << result2 << " -- correct\n";
  }

  return testStatus;
}
