// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <eq_ord_show.h>

#include <iostream>
#include <string>

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
  // Test Eq class
  ASSERT(test_eq_true == true);
  ASSERT(test_eq_false == false);

  // Test neqb
  ASSERT(test_neq_true == true);
  ASSERT(test_neq_false == false);

  // Test Ord class (lt)
  ASSERT(test_lt_true == true);
  ASSERT(test_lt_false == false);

  // Test compare function
  ASSERT(test_compare_lt == Ordering::LT);
  ASSERT(test_compare_eq == Ordering::EQ);
  ASSERT(test_compare_gt == Ordering::GT);

  // Test Show class
  ASSERT(test_show == "<nat>");

  if (testStatus == 0) {
    std::cout << "All tests passed!" << std::endl;
  }

  return testStatus;
}
