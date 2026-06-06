// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for double-call UB in the Datatypes.app extraction template.
//
// The Datatypes.app template in Mapping/DequeList.v is:
//   "[&]() { auto _r = %a0; _r.insert(_r.end(), %a1.begin(), %a1.end()); return _r; }()"
//
// When %a1 is a function-call expression like gen_list(b), the placeholder is
// substituted *twice*:
//   _r.insert(_r.end(), gen_list(b).begin(), gen_list(b).end());
//                       ^^^^^^^^^^^              ^^^^^^^^^^^
//                       first call (T1)          second call (T2)
//
// The insert receives T1.begin() and T2.end() -- iterators from different
// deque instances.  std::deque::iterator::operator== compares raw __cur
// pointers.  After advancing T1.begin() n times (where n = gen_list(b).size()),
// __cur points to address (T1.data + n), while T2.end().__cur = (T2.data + n).
// Since T1.data != T2.data, the comparison never returns true at the correct
// position, causing the insert to read past T1's storage boundary -- UB.
//
// The fix is to store %a1 in a named temporary:
//   auto _s = %a1; _r.insert(_r.end(), _s.begin(), _s.end());
//
// This test calls concat_two(3, 2) and checks that the result is exactly
// {3, 2, 1, 2, 1}.  With the bug, the insert reads past gen_list(2)'s storage,
// causing either wrong results or a crash (SIGSEGV), both of which fail the test.

#include "app_doublecall.h"

#include <deque>
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
  // concat_two(3, 2) should produce gen_list(3) ++ gen_list(2)
  //   = {3, 2, 1} ++ {2, 1} = {3, 2, 1, 2, 1}
  //
  // With the double-call bug, the insert iterates from T1.begin() to T2.end()
  // where T1 and T2 are different deque instances.  The comparison never
  // returns true at the correct position, so the insert reads past T1's
  // storage, producing wrong results or crashing.
  auto result = AppDoublecall::concat_two(3, 2);

  ASSERT(result.size() == 5);
  if (result.size() >= 5) {
    ASSERT(result[0] == 3);
    ASSERT(result[1] == 2);
    ASSERT(result[2] == 1);
    ASSERT(result[3] == 2);
    ASSERT(result[4] == 1);
  }

  if (testStatus == 0) {
    std::cout << "concat_two(3, 2) = {";
    for (size_t i = 0; i < result.size(); ++i) {
      if (i) std::cout << ", ";
      std::cout << result[i];
    }
    std::cout << "} -- correct\n";
  }

  return testStatus;
}
