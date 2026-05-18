// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "let_fix_ycomb_byref.h"

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
    ASSERT(LetFixYcombByref::test_sum == 15);
    std::cout << "Test 1 (sum_list): PASSED" << std::endl;
  }

  // Test 2: zip_sum [1;2;3] [10;20;30] = [11;22;33]
  {
    ASSERT(list_nth(LetFixYcombByref::test_zip, 0) == 11);
    ASSERT(list_nth(LetFixYcombByref::test_zip, 1) == 22);
    ASSERT(list_nth(LetFixYcombByref::test_zip, 2) == 33);
    std::cout << "Test 2 (zip_sum): PASSED" << std::endl;
  }

  // Test 3: countdown 3 = [3; 2; 1]
  {
    ASSERT(list_nth(LetFixYcombByref::test_countdown, 0) == 3);
    ASSERT(list_nth(LetFixYcombByref::test_countdown, 1) == 2);
    ASSERT(list_nth(LetFixYcombByref::test_countdown, 2) == 1);
    std::cout << "Test 3 (countdown): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll let_fix_ycomb_byref tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
