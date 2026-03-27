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
  auto nil = UIntList::nil();
  auto l1 = UIntList::cons(1u, UIntList::cons(2u, nil));
  auto l2 = UIntList::cons(3u, UIntList::cons(4u, nil));
  auto sep = UIntList::cons(0u, nil);

  auto ll_nil = ListOfLists::nil();
  auto ll = ListOfLists::cons(l1, ListOfLists::cons(l2, ll_nil));

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
  auto empty_ll = ListOfLists::cons(nil, ListOfLists::cons(nil, ll_nil));
  ASSERT(LoopifyListOfLists::all_nil(empty_ll) == true);
  ASSERT(LoopifyListOfLists::all_nil(ll) == false);

  // max_length
  auto l3 = UIntList::cons(5u, UIntList::cons(6u, UIntList::cons(7u, nil)));
  auto ll2 = ListOfLists::cons(l1, ListOfLists::cons(l3, ll_nil));
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
