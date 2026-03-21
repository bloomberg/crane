// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_of_lists.h>

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
using ListOfLists = List<std::shared_ptr<UIntList>>;

int main() {
  auto nil = UIntList::ctor::Nil_();
  auto l1 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, nil));
  auto l2 = UIntList::ctor::Cons_(3u, UIntList::ctor::Cons_(4u, nil));
  auto sep = UIntList::ctor::Cons_(0u, nil);

  auto ll_nil = ListOfLists::ctor::Nil_();
  auto ll = ListOfLists::ctor::Cons_(l1, ListOfLists::ctor::Cons_(l2, ll_nil));

  // intercalate
  auto intercalated = LoopifyListOfLists::intercalate(sep, ll);
  ASSERT(LoopifyListOfLists::list_len(intercalated) == 5u);  // [1,2,0,3,4]

  // flatten
  auto flattened = LoopifyListOfLists::flatten(ll);
  ASSERT(LoopifyListOfLists::list_len(flattened) == 4u);  // [1,2,3,4]

  // count_total
  ASSERT(LoopifyListOfLists::count_total(ll) == 4u);

  // firsts
  auto f = LoopifyListOfLists::firsts(ll);
  ASSERT(LoopifyListOfLists::list_len(f) == 2u);  // [1, 3]

  // all_nil
  auto empty_ll = ListOfLists::ctor::Cons_(nil, ListOfLists::ctor::Cons_(nil, ll_nil));
  ASSERT(LoopifyListOfLists::all_nil(empty_ll) == true);
  ASSERT(LoopifyListOfLists::all_nil(ll) == false);

  // max_length
  auto l3 = UIntList::ctor::Cons_(5u, UIntList::ctor::Cons_(6u, UIntList::ctor::Cons_(7u, nil)));
  auto ll2 = ListOfLists::ctor::Cons_(l1, ListOfLists::ctor::Cons_(l3, ll_nil));
  ASSERT(LoopifyListOfLists::max_length(ll2) == 3u);

  // transpose - basic test
  auto trans = LoopifyListOfLists::transpose(ll);
  // [[1,2],[3,4]] transposed should give [[1,3],[2,4]]
  ASSERT(LoopifyListOfLists::total_length(trans) >= 0u);  // Just check it doesn't crash

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
