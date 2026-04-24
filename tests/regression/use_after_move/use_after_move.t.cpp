// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <use_after_move.h>

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
  std::cout << "Testing use-after-move patterns...\n";

  UseAfterMove::State s{42, 99, 1};

  // Pattern 1: Record with projection
  auto p1 = UseAfterMove::pattern1(s);
  ASSERT(p1.first.value == 42);
  ASSERT(p1.second == 42);
  std::cout << "  pattern1: OK\n";

  // Pattern 2: Two projections (nested pair)
  auto p2 = UseAfterMove::pattern2(s);
  ASSERT(p2.first.first.value == 42);
  ASSERT(p2.first.second == 42);
  ASSERT(p2.second == 99);
  std::cout << "  pattern2: OK\n";

  // Pattern 3: Nested pair
  auto p3 = UseAfterMove::pattern3(s);
  ASSERT(p3.first.first.value == 42);
  ASSERT(p3.first.second == 42);
  ASSERT(p3.second == 99);
  std::cout << "  pattern3: OK\n";

  // Pattern 4: Let-bound
  auto p4 = UseAfterMove::pattern4(s);
  ASSERT(p4.first.value == 42);
  ASSERT(p4.second == 42);
  std::cout << "  pattern4: OK\n";

  // Pattern 5: Chain of lets
  auto p5 = UseAfterMove::pattern5(s);
  ASSERT(p5.first.value == 42);
  ASSERT(p5.second == 42);
  std::cout << "  pattern5: OK\n";

  // Pattern 6: If-then-else
  auto p6 = UseAfterMove::pattern6(s);
  ASSERT(p6.first.value == 42);
  ASSERT(p6.second == 99);  // flag is 1, so else branch with data
  std::cout << "  pattern6: OK\n";

  // Pattern 7: Nested pairs (3 levels)
  auto p7 = UseAfterMove::pattern7(s);
  ASSERT(p7.first.first.first.value == 42);
  ASSERT(p7.first.first.second == 42);
  ASSERT(p7.first.second == 99);
  ASSERT(p7.second == 1);
  std::cout << "  pattern7: OK\n";

  std::cout << "All tests passed!\n";
  return testStatus;
}
