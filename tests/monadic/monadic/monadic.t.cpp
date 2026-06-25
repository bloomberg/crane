// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "monadic.h"

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
  // Test 1: option_return
  {
    ASSERT(Monadic::test_return.has_value());
    ASSERT(*Monadic::test_return == 42);
    std::cout << "Test 1 (option_return 42): PASSED" << std::endl;
  }

  // Test 2: option_bind Some
  {
    ASSERT(Monadic::test_bind_some.has_value());
    ASSERT(*Monadic::test_bind_some == 11);
    std::cout << "Test 2 (bind Some 10 (+1)): PASSED" << std::endl;
  }

  // Test 3: option_bind None
  {
    ASSERT(!Monadic::test_bind_none.has_value());
    std::cout << "Test 3 (bind None (+1)): PASSED" << std::endl;
  }

  // Test 4: safe_div ok
  {
    ASSERT(Monadic::test_safe_div_ok.has_value());
    ASSERT(*Monadic::test_safe_div_ok == 3);
    std::cout << "Test 4 (safe_div 10 3): PASSED" << std::endl;
  }

  // Test 5: safe_div zero
  {
    ASSERT(!Monadic::test_safe_div_zero.has_value());
    std::cout << "Test 5 (safe_div 10 0): PASSED" << std::endl;
  }

  // Test 6: chained bind ok
  {
    ASSERT(Monadic::test_chain_ok.has_value());
    ASSERT(*Monadic::test_chain_ok == 3);
    std::cout << "Test 6 (div_then_sub 20 4 2): PASSED" << std::endl;
  }

  // Test 7: chained bind fail
  {
    ASSERT(!Monadic::test_chain_fail.has_value());
    std::cout << "Test 7 (div_then_sub 20 0 2): PASSED" << std::endl;
  }

  // Test 8: fib 5 is correct
  {
    ASSERT(Monadic::test_state_fib == 5);
    std::cout << "Test 8 (fib 5 returns 5): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll monadic tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
