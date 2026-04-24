// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <record_field_patterns.h>

#include <cassert>
#include <iostream>
#include <memory>

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
  // 1. Field-value matching
  ASSERT(RecordFieldPatterns::test_origin == 0);
  ASSERT(RecordFieldPatterns::test_y_axis == 1);
  ASSERT(RecordFieldPatterns::test_x_axis == 2);
  ASSERT(RecordFieldPatterns::test_general == 7);
  ASSERT(RecordFieldPatterns::test_zero_x == 42);
  ASSERT(RecordFieldPatterns::test_nonzero == 14);  // S 4 + 10

  // 2. Record through polymorphic identity
  ASSERT(RecordFieldPatterns::test_id.px == 99);
  ASSERT(RecordFieldPatterns::test_id.py == 1);

  // 3. Section-parameterized function over record
  ASSERT(RecordFieldPatterns::test_labeled == 90);  // 3 * (10 + 20)

  // 4. Functor-abstracted record
  ASSERT(RecordFieldPatterns::test_functor == 300);

  // 5. Nested record destructuring
  //    segment (1,2)→(4,6): dx=3, dy=4, 9+16=25
  ASSERT(RecordFieldPatterns::test_seg == 25);

  // 7. Higher-order projection
  ASSERT(RecordFieldPatterns::test_sum == 60);

  // 8. Swap
  ASSERT(RecordFieldPatterns::test_swap.px == 7);
  ASSERT(RecordFieldPatterns::test_swap.py == 3);

  // 9. Type-valued field record
  ASSERT(RecordFieldPatterns::test_container == 5);

  std::cout << "All record field pattern tests passed" << std::endl;
  return testStatus;
}
