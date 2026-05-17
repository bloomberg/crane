// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Test: Top-level fixpoint with state-threading pair return uses std::move.
#include "fix_state_threading.h"
#include <iostream>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) ++testStatus;
  }
}

template <typename A>
A list_nth(const List<A> &l, unsigned int n) {
  const List<A> *cur = &l;
  for (unsigned int i = 0; i < n; ++i) {
    cur = std::get<typename List<A>::Cons>(cur->v()).a1.get();
  }
  return std::get<typename List<A>::Cons>(cur->v()).a0;
}
} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // reverse_count [1;2;3] [] = ([3;2;1], 3)
  ASSERT(FixStateThreading::test_rev.second == 3u);
  ASSERT(list_nth(FixStateThreading::test_rev.first, 0) == 3u);
  ASSERT(list_nth(FixStateThreading::test_rev.first, 1) == 2u);
  ASSERT(list_nth(FixStateThreading::test_rev.first, 2) == 1u);
  std::cout << "Test 1 (reverse_count): PASSED" << std::endl;

  // collect_odds_evens [1;2;3;4;5] [] [] = ([5;3;1], [4;2])
  ASSERT(list_nth(FixStateThreading::test_ce.first, 0) == 5u);
  ASSERT(list_nth(FixStateThreading::test_ce.first, 1) == 3u);
  ASSERT(list_nth(FixStateThreading::test_ce.first, 2) == 1u);
  ASSERT(list_nth(FixStateThreading::test_ce.second, 0) == 4u);
  ASSERT(list_nth(FixStateThreading::test_ce.second, 1) == 2u);
  std::cout << "Test 2 (collect_odds_evens): PASSED" << std::endl;

  // sum_with_acc [10;20;30] 0 = (60, 3)
  ASSERT(FixStateThreading::test_sum.first == 60u);
  ASSERT(FixStateThreading::test_sum.second == 3u);
  std::cout << "Test 3 (sum_with_acc): PASSED" << std::endl;

  if (testStatus == 0) {
    std::cout << "\nAll fix_state_threading tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
