// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "mutual_coind.h"

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
  // Test 1: headA of countA(0) == 0
  {
    ASSERT(MutualCoind::test_headA == 0);
    std::cout << "Test 1 (headA countA 0): PASSED" << std::endl;
  }

  // Test 2: headB of countB(10) == 10
  {
    ASSERT(MutualCoind::test_headB == 10);
    std::cout << "Test 2 (headB countB 10): PASSED" << std::endl;
  }

  // Test 3: takeA 5 (countA 0) == [0,1,2,3,4]
  {
    const List<unsigned int> *l = &MutualCoind::test_take5;
    unsigned int expected[] = {0, 1, 2, 3, 4};
    for (int i = 0; i < 5; i++) {
      auto &vr = l->v();
      ASSERT(std::holds_alternative<List<unsigned int>::Cons>(vr));
      auto &c = std::get<List<unsigned int>::Cons>(vr);
      ASSERT(c.d_a0 == expected[i]);
      l = c.d_a1.get();
    }
    ASSERT(std::holds_alternative<List<unsigned int>::Nil>(l->v()));
    std::cout << "Test 3 (takeA 5): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll mutual_coind tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
