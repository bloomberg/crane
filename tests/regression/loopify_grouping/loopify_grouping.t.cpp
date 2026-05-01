// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_grouping.h>

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

int main() {
  auto nil = UIntList::nil();
  auto l_sorted = UIntList::cons(1u, UIntList::cons(1u, UIntList::cons(
    2u, UIntList::cons(2u, UIntList::cons(3u, nil)))));
  auto l_dups = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    1u, UIntList::cons(3u, UIntList::cons(2u, nil)))));

  // group
  auto grouped = LoopifyGrouping::group(l_sorted);

  // elem
  ASSERT(LoopifyGrouping::elem(2u, l_sorted) == true);
  ASSERT(LoopifyGrouping::elem(99u, l_sorted) == false);

  // nub
  auto unique = LoopifyGrouping::nub(l_dups);

  // remove_elem
  auto removed = LoopifyGrouping::remove_elem(1u, l_dups);

  // partition3
  auto l5 = UIntList::cons(1u, UIntList::cons(5u, UIntList::cons(
    3u, UIntList::cons(7u, UIntList::cons(3u, nil)))));
  auto partitioned = LoopifyGrouping::partition3(3u, l5);

  // count_elem
  ASSERT(LoopifyGrouping::count_elem(1u, l_dups) == 2u);

  // group_pairs
  auto pairs = LoopifyGrouping::group_pairs(l5);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
