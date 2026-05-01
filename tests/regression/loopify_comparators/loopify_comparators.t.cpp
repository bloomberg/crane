// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_comparators.h>

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
  auto l5 = UIntList::cons(3u, UIntList::cons(1u, UIntList::cons(
    4u, UIntList::cons(1u, UIntList::cons(5u, nil)))));
  auto l_sorted = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    3u, UIntList::cons(4u, UIntList::cons(5u, nil)))));

  // maximum_by
  ASSERT(LoopifyComparators::maximum_by(l5) == 5u);

  // minimum_by
  ASSERT(LoopifyComparators::minimum_by(l5) == 1u);

  // merge_by
  auto merged = LoopifyComparators::merge_by(l_sorted, l_sorted);

  // insert_sorted
  auto inserted = LoopifyComparators::insert_sorted(3u, l_sorted);

  // insertion_sort
  auto sorted = LoopifyComparators::insertion_sort(l5);

  // is_sorted
  ASSERT(LoopifyComparators::is_sorted(l_sorted) == true);
  ASSERT(LoopifyComparators::is_sorted(l5) == false);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
