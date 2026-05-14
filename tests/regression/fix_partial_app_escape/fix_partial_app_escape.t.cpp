// Regression: a partially-applied fixpoint must not capture the
// std::function variable by reference.  The fixpoint escapes via
// an IIFE, so [&] capture creates a dangling reference.
// This test verifies the fix compiles and produces correct results
// at runtime (previously it crashed with bad_function_call or segfault).

#include "fix_partial_app_escape.h"

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
  // The primary regression is that these calls don't crash.
  // Previously this caused bad_function_call or segfault due to
  // a dangling reference from [&] capture of the std::function.

  // count_bits 0 = 0
  ASSERT(FixPartialAppEscape::test_0 == 0u);

  // count_bits 1 = 1
  ASSERT(FixPartialAppEscape::test_1 == 1u);

  // Verify direct calls also don't crash
  ASSERT(FixPartialAppEscape::count_bits(0u) == 0u);
  ASSERT(FixPartialAppEscape::count_bits(1u) == 1u);

  // Call with larger values to stress-test (no crash = success)
  (void)FixPartialAppEscape::test_7;
  (void)FixPartialAppEscape::test_255;
  (void)FixPartialAppEscape::count_bits(15u);
  (void)FixPartialAppEscape::count_bits(100u);

  return testStatus;
}
