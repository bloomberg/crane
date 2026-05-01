// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "partial_apply.h"

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

template <typename A>
A list_nth(const List<A> &l, unsigned int n) {
  const List<A> *cur = &l;
  for (unsigned int i = 0; i < n; ++i) {
    auto &c = std::get<typename List<A>::Cons>(cur->v());
    cur = c.d_a1.get();
  }
  return std::get<typename List<A>::Cons>(cur->v()).d_a0;
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // Test 1: inc_all (map S [1;2;3] = [2;3;4])
  {
    ASSERT(list_nth(PartialApply::test_inc, 0) == 2);
    ASSERT(list_nth(PartialApply::test_inc, 1) == 3);
    ASSERT(list_nth(PartialApply::test_inc, 2) == 4);
    std::cout << "Test 1 (inc_all): PASSED" << std::endl;
  }

  // Test 2: tag_all (map (pair 1) [10;20;30])
  {
    auto p = list_nth(PartialApply::test_tag, 0);
    ASSERT(p.first == 1);
    ASSERT(p.second == 10);
    std::cout << "Test 2 (tag_all): PASSED" << std::endl;
  }

  // Test 3: sum_with_init (100 + 1 + 2 + 3 = 106)
  {
    ASSERT(PartialApply::test_sum == 106);
    std::cout << "Test 3 (sum_with_init): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll partial_apply tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
