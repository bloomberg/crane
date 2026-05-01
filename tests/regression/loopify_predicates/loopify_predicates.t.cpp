// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_predicates.h>

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
  auto l5 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    3u, UIntList::cons(4u, UIntList::cons(5u, nil)))));

  auto is_small = [](unsigned int x) { return x < 3; };
  auto is_even = [](unsigned int x) { return x % 2 == 0; };
  auto eq = [](unsigned int x, unsigned int y) { return x == y; };

  // take_while
  auto taken = LoopifyPredicates::take_while(is_small, l5);

  // drop_while
  auto dropped = LoopifyPredicates::drop_while(is_small, l5);

  // span
  auto spanned = LoopifyPredicates::span(is_small, l5);

  // break_at
  auto broken = LoopifyPredicates::break_at(is_small, l5);

  // filter
  auto filtered = LoopifyPredicates::filter(is_even, l5);

  // reject
  auto rejected = LoopifyPredicates::reject(is_even, l5);

  // forall_pred
  ASSERT(LoopifyPredicates::forall_pred(is_small, nil) == true);
  auto l_small = UIntList::cons(1u, UIntList::cons(2u, nil));
  ASSERT(LoopifyPredicates::forall_pred(is_small, l_small) == true);
  ASSERT(LoopifyPredicates::forall_pred(is_small, l5) == false);

  // exists_pred
  ASSERT(LoopifyPredicates::exists_pred(is_even, nil) == false);
  ASSERT(LoopifyPredicates::exists_pred(is_even, l5) == true);

  // find_index
  auto idx = LoopifyPredicates::find_index(is_even, l5);
  ASSERT(idx && *idx == 1u);

  // find_indices
  auto indices = LoopifyPredicates::find_indices(is_even, l5);

  // delete_by
  auto deleted = LoopifyPredicates::delete_by(eq, 3u, l5);

  // remove_all
  auto l_dups = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    1u, UIntList::cons(3u, UIntList::cons(1u, nil)))));
  auto removed = LoopifyPredicates::remove_all(1u, l_dups);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
