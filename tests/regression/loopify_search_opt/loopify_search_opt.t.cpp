// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_search_opt.h>

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
  auto nil = UIntList::nil();

  // lis - longest increasing subsequence
  auto l1 = UIntList::cons(1u, UIntList::cons(3u, UIntList::cons(2u,
    UIntList::cons(4u, nil))));
  auto lis_result = LoopifySearchOpt::lis(l1);

  // longest_run
  auto l2 = UIntList::cons(1u, UIntList::cons(1u, UIntList::cons(2u,
    UIntList::cons(2u, UIntList::cons(2u, UIntList::cons(3u, nil))))));
  auto run = LoopifySearchOpt::longest_run(l2);

  // knapsack
  auto items_nil = PairList::nil();
  auto items = PairList::cons(std::make_pair(2u, 3u),
    PairList::cons(std::make_pair(3u, 4u),
    PairList::cons(std::make_pair(4u, 5u), items_nil)));
  ASSERT(LoopifySearchOpt::knapsack(5u, items) >= 0u);

  // subset_sum
  auto l3 = UIntList::cons(3u, UIntList::cons(5u, UIntList::cons(7u, nil)));
  ASSERT(LoopifySearchOpt::subset_sum(8u, l3) == true);   // 3+5
  ASSERT(LoopifySearchOpt::subset_sum(12u, l3) == true);  // 5+7
  ASSERT(LoopifySearchOpt::subset_sum(2u, l3) == false);

  // majority
  auto l4 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(1u,
    UIntList::cons(1u, nil))));
  auto maj = LoopifySearchOpt::majority(l4);
  ASSERT(maj.first == 1u);  // candidate

  // binary_search (on sorted list)
  auto sorted = UIntList::cons(1u, UIntList::cons(3u, UIntList::cons(5u,
    UIntList::cons(7u, UIntList::cons(9u, nil)))));
  ASSERT(LoopifySearchOpt::binary_search(5u, sorted) == true);
  ASSERT(LoopifySearchOpt::binary_search(4u, sorted) == false);
  ASSERT(LoopifySearchOpt::binary_search(9u, sorted) == true);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
