// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "let_fix.h"

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
  // Test 1: local_sum [1;2;3;4;5] = 15
  {
    ASSERT(LetFix::test_sum == 15);
    std::cout << "Test 1 (local_sum): PASSED" << std::endl;
  }

  // Test 2: local_rev [1;2;3] = [3;2;1]
  {
    ASSERT(list_nth(LetFix::test_rev, 0) == 3);
    ASSERT(list_nth(LetFix::test_rev, 1) == 2);
    ASSERT(list_nth(LetFix::test_rev, 2) == 1);
    std::cout << "Test 2 (local_rev): PASSED" << std::endl;
  }

  // Test 3: local_mem
  {
    ASSERT(LetFix::test_mem_found == true);
    ASSERT(LetFix::test_mem_missing == false);
    std::cout << "Test 3 (local_mem): PASSED" << std::endl;
  }

  // Test 4: local_flatten [[1;2];[3];[4;5;6]] = [1;2;3;4;5;6]
  {
    ASSERT(list_nth(LetFix::test_flatten, 0) == 1);
    ASSERT(list_nth(LetFix::test_flatten, 5) == 6);
    std::cout << "Test 4 (local_flatten): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll let_fix tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
