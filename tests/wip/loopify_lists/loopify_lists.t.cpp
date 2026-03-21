// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <functional>
#include <iostream>
#include <loopify_lists.h>

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
  using List = LoopifyLists::list<unsigned int>;

  // Build [1, 2, 3]
  auto l3 = List::ctor::Cons_(
      1u, List::ctor::Cons_(2u, List::ctor::Cons_(3u, List::ctor::Nil_())));

  // Test stutter: [1,2,3] -> [1,1,2,2,3,3]
  auto stuttered = LoopifyLists::stutter(l3);
  ASSERT(stuttered != nullptr);

  // Test snoc
  auto snocced = LoopifyLists::snoc(l3, 4u);
  ASSERT(snocced != nullptr);

  // Test intersperse
  auto interspered = LoopifyLists::intersperse(0u, l3);
  ASSERT(interspered != nullptr);

  // Test replicate
  auto reps = LoopifyLists::replicate(5u, 7u);
  ASSERT(reps != nullptr);

  // Test range
  auto r = LoopifyLists::range(0u, 5u);
  ASSERT(r != nullptr);

  // Test scanl
  auto scanned = LoopifyLists::scanl<unsigned int, unsigned int>(
      [](unsigned int a, unsigned int b) { return a + b; }, 0u, l3);
  ASSERT(scanned != nullptr);

  // Test step_sum: [2,3,4] -> 2 + 3*2 + 4 = 2 + 6 + 4 = 12
  auto nums = List::ctor::Cons_(
      2u, List::ctor::Cons_(3u, List::ctor::Cons_(4u, List::ctor::Nil_())));
  ASSERT(LoopifyLists::step_sum(nums) == 12u);

  // Test sum_abs (absolute differences from base)
  auto abs_sum = LoopifyLists::sum_abs(l3, 0u);
  ASSERT(abs_sum > 0u);

  // Test four_elem
  auto four = List::ctor::Cons_(
      1u, List::ctor::Cons_(
              2u, List::ctor::Cons_(
                      3u, List::ctor::Cons_(
                              4u, List::ctor::Cons_(5u, List::ctor::Nil_())))));
  auto result = LoopifyLists::four_elem(four);
  ASSERT(result == 11u); // 1+2+3+4 + four_elem([5]) = 10 + 1

  // Test between: filter [1,2,3] in range [1,2] -> [1,2]
  auto filtered = LoopifyLists::between(1u, 2u, l3);
  ASSERT(filtered != nullptr);

  // Test count_matching: count even numbers in [2,3,4]
  auto count = LoopifyLists::count_matching(
      [](unsigned int x) { return x % 2 == 0; }, nums);
  ASSERT(count == 2u); // 2 and 4 are even

  // Test categorize with key=3: [2,3,4] -> 1 + 2 + 3 = 6
  auto cat = LoopifyLists::categorize(3u, nums);
  ASSERT(cat == 6u);

  // Test max_prefix_sum
  auto max_ps = LoopifyLists::max_prefix_sum(l3);
  ASSERT(max_ps > 0u);

  // Test pairwise_sum: [1,2,3] -> [3,5]
  auto pairs = LoopifyLists::pairwise_sum(l3);
  ASSERT(pairs != nullptr);

  // Test weighted_sum: weighted_sum(0, [1,2,3]) = 0*1 + 1*2 + 2*3 = 8
  auto ws = LoopifyLists::weighted_sum(0u, l3);
  ASSERT(ws == 8u);

  std::cout << "All unique list tests passed!\n";
  return testStatus;
}
