// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for envE effects.

#include <env.h>

#include <cassert>
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

#define ASSERT(X) aSsErT(!(X), #X, __LINE__)

void test_set_and_get() {
  auto result = Env::set_and_get("CRANE_TEST_ENV_1", "hello");
  ASSERT(result.has_value());
  ASSERT(*result == "hello");
  std::cout << "PASS: set_and_get\n";
}

void test_set_unset_get() {
  auto result = Env::set_unset_get("CRANE_TEST_ENV_2", "world");
  ASSERT(!result.has_value());
  std::cout << "PASS: set_unset_get\n";
}

void test_get_missing() {
  auto result = Env::get_missing("CRANE_NONEXISTENT_VAR_XYZ_999");
  ASSERT(!result.has_value());
  std::cout << "PASS: get_missing\n";
}

int main() {
  test_set_and_get();
  test_set_unset_get();
  test_get_missing();

  std::cout << (testStatus ? "FAIL" : "PASS") << ": env\n";
  return testStatus;
}
