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
  auto nil = UIntList::ctor::Nil_();
  auto l3 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(3u, nil)));

  // process_twice
  auto processed = LoopifySpecialRecursion::process_twice(l3);
  ASSERT(processed != nullptr);

  // double_append
  auto doubled = LoopifySpecialRecursion::double_append(l3, nil);
  ASSERT(doubled != nullptr);

  // remove_if_sum_even
  auto removed = LoopifySpecialRecursion::remove_if_sum_even(l3);
  ASSERT(removed != nullptr);

  // reverse_insert
  auto inserted = LoopifySpecialRecursion::reverse_insert(2u, l3);
  ASSERT(inserted != nullptr);

  // nest_apply
  auto inc = [](unsigned int x) { return x + 1; };
  ASSERT(LoopifySpecialRecursion::nest_apply(0u, inc, 5u) == 5u);
  ASSERT(LoopifySpecialRecursion::nest_apply(3u, inc, 5u) == 8u);

  // collect_sorted
  using tree = LoopifySpecialRecursion::tree;
  auto leaf = tree::ctor::Leaf_();
  auto t = tree::ctor::Node_(leaf, 5u, leaf);
  auto collected = LoopifySpecialRecursion::collect_sorted(t);
  ASSERT(collected != nullptr);

  // sum_odd_indices
  auto l5 = UIntList::ctor::Cons_(10u, UIntList::ctor::Cons_(20u, UIntList::ctor::Cons_(
    30u, UIntList::ctor::Cons_(40u, UIntList::ctor::Cons_(50u, nil)))));
  ASSERT(LoopifySpecialRecursion::sum_odd_indices(l5) == 60u);  // indices 1,3 -> 20+40

  // categorize_by
  ASSERT(LoopifySpecialRecursion::categorize_by(2u, l3) == 6u);  // 1<2:1, 2==2:2, 3>2:3

  // between
  auto filtered = LoopifySpecialRecursion::between(2u, 4u, l5);
  ASSERT(filtered != nullptr);

  // merge_levels
  auto ll_nil = List<std::shared_ptr<UIntList>>::ctor::Nil_();
  auto ll = List<std::shared_ptr<UIntList>>::ctor::Cons_(l3,
    List<std::shared_ptr<UIntList>>::ctor::Cons_(l3, ll_nil));
  auto merged = LoopifySpecialRecursion::merge_levels(ll);
  ASSERT(merged != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
