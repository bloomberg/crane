// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for ITree-based effect composition.
// Verifies parE + consoleE compose and generate correct C++.

#include <effect_compose.h>

#include <cassert>
#include <future>
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

void test_par_double() {
  auto n = EffectCompose::par_double(21u);
  ASSERT(n == 42u);
  std::cout << "PASS: par_double (parE + consoleE composition)\n";
}

void test_par_add() {
  // double(10) + double(11) = 20 + 22 = 42
  auto n = EffectCompose::par_add(10u, 11u);
  ASSERT(n == 42u);
  std::cout << "PASS: par_add (two parallel futures)\n";
}

void test_par_compute_and_greet() {
  auto n = EffectCompose::par_compute_and_greet(99u);
  ASSERT(n == 100u);
  std::cout << "PASS: par_compute_and_greet (parE + consoleE interleaved)\n";
}

int main() {
  test_par_double();
  test_par_add();
  test_par_compute_and_greet();

  std::cout << (testStatus ? "FAIL" : "PASS")
            << ": effect_compose\n";
  return testStatus;
}
