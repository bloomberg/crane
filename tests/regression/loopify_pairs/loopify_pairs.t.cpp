// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_pairs.h>

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
  using List = LoopifyPairs::list<unsigned int>;

  auto l = List::cons(
      1u, List::cons(2u, List::cons(3u, List::nil())));

  // Test unique pair operations
  auto gt1 = [](unsigned int x) { return x > 1; };
  auto partitioned = LoopifyPairs::partition(gt1, l);

  auto l2 = List::cons(
      4u, List::cons(5u, List::cons(6u, List::nil())));
  auto zipped = LoopifyPairs::zip(l, l2);

  auto split = LoopifyPairs::split_at(2u, l);

  auto sw = LoopifyPairs::swizzle(l);

  auto mm = LoopifyPairs::min_max(l);
  ASSERT(mm.first == 1u);
  ASSERT(mm.second == 3u);

  auto sc = LoopifyPairs::sum_and_count(l);
  ASSERT(sc.first == 6u);
  ASSERT(sc.second == 3u);

  auto spc = LoopifyPairs::sum_prod_count(l);
  ASSERT(spc.first == 6u);

  std::cout << "All unique pair tests passed!\n";
  return testStatus;
}
