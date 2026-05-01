// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_special_recursion.h>

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
  auto l3 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(3u, nil)));

  // process_twice
  auto processed = LoopifySpecialRecursion::process_twice(l3);

  // double_append
  auto doubled = LoopifySpecialRecursion::double_append(l3, nil);

  // remove_if_sum_even
  auto removed = LoopifySpecialRecursion::remove_if_sum_even(l3);

  // reverse_insert
  auto inserted = LoopifySpecialRecursion::reverse_insert(2u, l3);

  // nest_apply
  auto inc = [](unsigned int x) { return x + 1; };
  ASSERT(LoopifySpecialRecursion::nest_apply(0u, inc, 5u) == 5u);
  ASSERT(LoopifySpecialRecursion::nest_apply(3u, inc, 5u) == 8u);

  // collect_sorted
  using tree = LoopifySpecialRecursion::tree;
  auto leaf = tree::leaf();
  auto t = tree::node(leaf, 5u, leaf);
  auto collected = LoopifySpecialRecursion::collect_sorted(t);

  // sum_odd_indices
  auto l5 = UIntList::cons(10u, UIntList::cons(20u, UIntList::cons(
    30u, UIntList::cons(40u, UIntList::cons(50u, nil)))));
  ASSERT(LoopifySpecialRecursion::sum_odd_indices(l5) == 60u);  // indices 1,3 -> 20+40

  // categorize_by
  ASSERT(LoopifySpecialRecursion::categorize_by(2u, l3) == 6u);  // 1<2:1, 2==2:2, 3>2:3

  // between
  auto filtered = LoopifySpecialRecursion::between(2u, 4u, l5);

  // merge_levels
  auto ll_nil = List<List<unsigned int>>::nil();
  auto ll = List<List<unsigned int>>::cons(l3,
    List<List<unsigned int>>::cons(l3, ll_nil));
  auto merged = LoopifySpecialRecursion::merge_levels(ll);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
