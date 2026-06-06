// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for missing any_cast when returning a type-erased sigT
// payload as a concrete template type.
//
// Regression: the generated extract_a<T1> S branch used to emit
// "return a1;" where a1 is std::any but the return type is T1.
// The fix inserts any_cast<T1>(a1) so the function compiles and runs.
//
// test_extract(x) calls extract_a<uint64_t> with existT _ 1 x (S branch),
// where payload_ty(S _) = A = uint64_t stored in std::any.
// Expected: test_extract(x) == x.

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
  // test_extract(x) = extract_a<uint64_t>(existT _ 1 x)
  // S branch: payload is x:uint64_t stored in std::any; any_cast<uint64_t>(a1) = x.
  uint64_t result = AnyCastNested::test_extract(42);
  ASSERT(result == 42);

  uint64_t result2 = AnyCastNested::test_extract(99);
  ASSERT(result2 == 99);

  if (testStatus == 0) {
    std::cout << "test_extract(42) = " << result << " (S-branch, expected 42)\n";
    std::cout << "test_extract(99) = " << result2 << " (S-branch, expected 99)\n";
  }

  return testStatus;
}
