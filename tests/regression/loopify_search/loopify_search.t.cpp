// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_search.h>

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

int main() {
  using List = ::List<unsigned int>;
  using PairList = ::List<std::pair<unsigned int, unsigned int>>;

  // Test knapsack
  auto item1 = std::make_pair(2u, 3u); // weight=2, value=3
  auto item2 = std::make_pair(3u, 4u); // weight=3, value=4
  auto item3 = std::make_pair(4u, 5u); // weight=4, value=5
  auto items = PairList::cons(
      item1, PairList::cons(
                 item2, PairList::cons(item3, PairList::nil())));
  auto value = LoopifySearch::knapsack(5u, items);
  ASSERT(value > 0u);

  // Test majority
  auto l = List::cons(
      1u, List::cons(
              2u, List::cons(
                      1u, List::cons(1u, List::nil()))));
  auto maj = LoopifySearch::majority(l);
  ASSERT(maj.first == 1u);

  // Test longest_increasing_subseq
  auto seq = List::cons(
      1u, List::cons(
              3u, List::cons(
                      2u, List::cons(4u, List::nil()))));
  auto lis = LoopifySearch::longest_increasing_subseq(seq);
  ASSERT(lis != nullptr);

  // Test maximum_by
  auto cmp = [](unsigned int x, unsigned int y) -> unsigned int {
    if (x == y)
      return 0u;
    if (x > y)
      return 1u;
    return 2u;
  };
  auto nums = List::cons(
      3u, List::cons(
              1u, List::cons(
                      4u, List::cons(2u, List::nil()))));
  auto max_val = LoopifySearch::maximum_by(cmp, nums);
  ASSERT(max_val == 4u);

  // Test binary_search
  auto sorted = List::cons(
      1u, List::cons(
              3u, List::cons(
                      5u, List::cons(
                              7u, List::cons(9u, List::nil())))));
  ASSERT(LoopifySearch::binary_search(5u, sorted));
  ASSERT(!LoopifySearch::binary_search(6u, sorted));

  // Test longest_run
  auto runs = List::cons(
      1u, List::cons(
              1u, List::cons(
                      2u, List::cons(
                              3u, List::cons(
                                      3u, List::cons(
                                              3u, List::nil()))))));
  auto longest = LoopifySearch::longest_run(runs);
  ASSERT(longest != nullptr);

  std::cout << "All search algorithm tests passed!\n";
  return testStatus;
}
