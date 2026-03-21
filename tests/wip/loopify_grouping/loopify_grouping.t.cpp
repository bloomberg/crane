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
  auto nil = UIntList::ctor::Nil_();
  auto l_sorted = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(
    2u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(3u, nil)))));
  auto l_dups = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(
    1u, UIntList::ctor::Cons_(3u, UIntList::ctor::Cons_(2u, nil)))));

  // group
  auto grouped = LoopifyGrouping::group(l_sorted);
  ASSERT(grouped != nullptr);

  // elem
  ASSERT(LoopifyGrouping::elem(2u, l_sorted) == true);
  ASSERT(LoopifyGrouping::elem(99u, l_sorted) == false);

  // nub
  auto unique = LoopifyGrouping::nub(l_dups);
  ASSERT(unique != nullptr);

  // remove_elem
  auto removed = LoopifyGrouping::remove_elem(1u, l_dups);
  ASSERT(removed != nullptr);

  // partition3
  auto l5 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(5u, UIntList::ctor::Cons_(
    3u, UIntList::ctor::Cons_(7u, UIntList::ctor::Cons_(3u, nil)))));
  auto partitioned = LoopifyGrouping::partition3(3u, l5);
  ASSERT(partitioned.first.first != nullptr && partitioned.first.second != nullptr && partitioned.second != nullptr);

  // count_elem
  ASSERT(LoopifyGrouping::count_elem(1u, l_dups) == 2u);

  // group_pairs
  auto pairs = LoopifyGrouping::group_pairs(l5);
  ASSERT(pairs != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
