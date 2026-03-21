// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_access.h>

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
using PairList = List<std::pair<unsigned int, unsigned int>>;

int main() {
  auto nil = UIntList::ctor::Nil_();
  auto l5 = UIntList::ctor::Cons_(10u, UIntList::ctor::Cons_(20u, UIntList::ctor::Cons_(
    30u, UIntList::ctor::Cons_(40u, UIntList::ctor::Cons_(50u, nil)))));

  // nth
  ASSERT(LoopifyListAccess::nth(0u, l5) == 10u);
  ASSERT(LoopifyListAccess::nth(2u, l5) == 30u);
  ASSERT(LoopifyListAccess::nth(4u, l5) == 50u);
  ASSERT(LoopifyListAccess::nth(10u, l5) == 0u);  // out of bounds

  // last
  ASSERT(LoopifyListAccess::last(nil) == 0u);
  ASSERT(LoopifyListAccess::last(l5) == 50u);

  // index_of
  ASSERT(LoopifyListAccess::index_of(30u, l5) == 2u);
  ASSERT(LoopifyListAccess::index_of(10u, l5) == 0u);
  ASSERT(LoopifyListAccess::index_of(99u, l5) == 0u);  // not found

  // member
  ASSERT(LoopifyListAccess::member(30u, l5) == true);
  ASSERT(LoopifyListAccess::member(99u, l5) == false);

  // lookup
  auto pairs_nil = PairList::ctor::Nil_();
  auto pairs = PairList::ctor::Cons_(std::make_pair(1u, 10u),
    PairList::ctor::Cons_(std::make_pair(2u, 20u),
    PairList::ctor::Cons_(std::make_pair(3u, 30u), pairs_nil)));
  ASSERT(LoopifyListAccess::lookup(2u, pairs) == 20u);
  ASSERT(LoopifyListAccess::lookup(5u, pairs) == 0u);  // not found

  // lookup_all
  auto pairs2 = PairList::ctor::Cons_(std::make_pair(1u, 10u),
    PairList::ctor::Cons_(std::make_pair(2u, 20u),
    PairList::ctor::Cons_(std::make_pair(1u, 11u), pairs_nil)));
  auto all_vals = LoopifyListAccess::lookup_all(1u, pairs2);
  ASSERT(all_vals != nullptr);

  // find
  auto is_big = [](unsigned int x) { return x > 35; };
  ASSERT(LoopifyListAccess::find(is_big, l5) == 40u);

  // count
  auto l_dups = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(
    1u, UIntList::ctor::Cons_(3u, UIntList::ctor::Cons_(1u, nil)))));
  ASSERT(LoopifyListAccess::count(1u, l_dups) == 3u);
  ASSERT(LoopifyListAccess::count(2u, l_dups) == 1u);

  // count_matching
  auto is_even = [](unsigned int x) { return x % 2 == 0; };
  ASSERT(LoopifyListAccess::count_matching(is_even, l5) == 5u);  // 10, 20, 30, 40, 50 -> all are even

  // nth_default
  ASSERT(LoopifyListAccess::nth_default(2u, 999u, l5) == 30u);
  ASSERT(LoopifyListAccess::nth_default(10u, 999u, l5) == 999u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
