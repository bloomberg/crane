// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for clockE effects.

#include <clock.h>

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

void test_now() {
  auto t = Clock::get_time();
  // Should be after 2000-01-01 in milliseconds
  ASSERT(t > 946684800000LL);
  std::cout << "PASS: now = " << t << " ms\n";
}

void test_steady() {
  auto t = Clock::get_steady();
  // steady_clock is monotonic (relative to system boot), just check non-negative
  ASSERT(t >= 0);
  std::cout << "PASS: steady_now = " << t << " ms\n";
}

void test_system() {
  auto t = Clock::get_system();
  ASSERT(t > 946684800000LL);
  std::cout << "PASS: system_now = " << t << " ms\n";
}

void test_elapsed() {
  auto dt = Clock::elapsed();
  // Two back-to-back steady_now calls — elapsed should be non-negative
  ASSERT(dt >= 0);
  std::cout << "PASS: elapsed = " << dt << " ms\n";
}

int main() {
  test_now();
  test_steady();
  test_system();
  test_elapsed();

  std::cout << (testStatus ? "FAIL" : "PASS") << ": clock\n";
  return testStatus;
}
