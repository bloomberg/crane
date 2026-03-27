// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_windows.h>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using UIntList = List<unsigned int>;
using UIntPairList = List<std::pair<unsigned int, unsigned int>>;
using ListOfLists = List<std::shared_ptr<UIntList>>;

int main() {
  auto nil = UIntList::nil();
  auto l3 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(3u, nil)));
  auto l5 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    3u, UIntList::cons(4u, UIntList::cons(5u, nil)))));

  // differences
  auto diffs = LoopifyListWindows::differences(l5);
  // [2-1, 3-2, 4-3, 5-4] = [1, 1, 1, 1]
  ASSERT(LoopifyListWindows::len(diffs) == 4u);

  // sliding_pairs
  auto pairs = LoopifyListWindows::sliding_pairs(l5);
  // [(1,2), (2,3), (3,4), (4,5)]
  ASSERT(pairs != nullptr);

  // take
  ASSERT(LoopifyListWindows::len(LoopifyListWindows::take(0u, l5)) == 0u);
  ASSERT(LoopifyListWindows::len(LoopifyListWindows::take(3u, l5)) == 3u);
  ASSERT(LoopifyListWindows::len(LoopifyListWindows::take(10u, l3)) == 3u);

  // inits
  auto ini = LoopifyListWindows::inits(l3);
  ASSERT(ini != nullptr);

  // tails
  auto tai = LoopifyListWindows::tails(l3);
  ASSERT(tai != nullptr);

  // windows
  auto wins = LoopifyListWindows::windows(3u, l5);
  ASSERT(wins != nullptr);

  // chunks
  auto chnks = LoopifyListWindows::chunks(2u, l5);
  ASSERT(chnks != nullptr);

  // group
  auto l_dups = UIntList::cons(1u, UIntList::cons(1u, UIntList::cons(
    2u, UIntList::cons(2u, UIntList::cons(2u, UIntList::cons(3u, nil))))));
  auto grouped = LoopifyListWindows::group(l_dups);
  ASSERT(grouped != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
