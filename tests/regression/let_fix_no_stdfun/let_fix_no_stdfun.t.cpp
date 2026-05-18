// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "let_fix_no_stdfun.h"

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
A list_nth(const List<A> &l, uint64_t n) {
  const List<A> *cur = &l;
  for (unsigned int i = 0; i < n; ++i) {
    auto &c = std::get<typename List<A>::Cons>(cur->v());
    cur = c.l.get();
  }
  return std::get<typename List<A>::Cons>(cur->v()).a;
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // Test 1: sum_list [1;2;3;4;5] = 15
  {
    ASSERT(LetFixNoStdfun::test_sum == 15);
    std::cout << "Test 1 (sum_list): PASSED" << std::endl;
  }

  // Test 2: flat_map_sum [[1;2]; [3]; [4;5;6]] = 1+2+3+4+5+6 = 21
  {
    ASSERT(LetFixNoStdfun::test_flat_map_sum == 21);
    std::cout << "Test 2 (flat_map_sum): PASSED" << std::endl;
  }

  // Test 3: flatten [[10;20]; [30]; [40;50]] = [10;20;30;40;50]
  {
    ASSERT(list_nth(LetFixNoStdfun::test_flatten, 0) == 10);
    ASSERT(list_nth(LetFixNoStdfun::test_flatten, 1) == 20);
    ASSERT(list_nth(LetFixNoStdfun::test_flatten, 2) == 30);
    ASSERT(list_nth(LetFixNoStdfun::test_flatten, 3) == 40);
    ASSERT(list_nth(LetFixNoStdfun::test_flatten, 4) == 50);
    std::cout << "Test 3 (flatten): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll let_fix_no_stdfun tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
