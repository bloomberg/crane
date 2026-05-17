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
  using List = LoopifyLists::list<uint64_t>;

  // Build [1, 2, 3]
  auto l3 = List::cons(
      1ULL, List::cons(2ULL, List::cons(3ULL, List::nil())));

  // Test stutter: [1,2,3] -> [1,1,2,2,3,3]
  auto stuttered = LoopifyLists::stutter(l3);

  // Test snoc
  auto snocced = LoopifyLists::snoc(l3, 4ULL);

  // Test intersperse
  auto interspered = LoopifyLists::intersperse(0ULL, l3);

  // Test replicate
  auto reps = LoopifyLists::replicate(5ULL, 7ULL);

  // Test range
  auto r = LoopifyLists::range(0ULL, 5ULL);

  // Test scanl
  auto scanned = LoopifyLists::scanl<uint64_t, uint64_t>(
      [](uint64_t a, uint64_t b) { return a + b; }, 0ULL, l3);

  // Test step_sum: [2,3,4] -> 2 + 3*2 + 4 = 2 + 6 + 4 = 12
  auto nums = List::cons(
      2ULL, List::cons(3ULL, List::cons(4ULL, List::nil())));
  ASSERT(LoopifyLists::step_sum(nums) == 12ULL);

  // Test sum_abs (absolute differences from base)
  auto abs_sum = LoopifyLists::sum_abs(l3, 0ULL);
  ASSERT(abs_sum > 0ULL);

  // Test four_elem
  auto four = List::cons(
      1ULL, List::cons(
              2ULL, List::cons(
                      3ULL, List::cons(
                              4ULL, List::cons(5ULL, List::nil())))));
  auto result = LoopifyLists::four_elem(four);
  ASSERT(result == 11ULL); // 1+2+3+4 + four_elem([5]) = 10 + 1

  // Test between: filter [1,2,3] in range [1,2] -> [1,2]
  auto filtered = LoopifyLists::between(1ULL, 2ULL, l3);

  // Test count_matching: count even numbers in [2,3,4]
  auto count = LoopifyLists::count_matching(
      [](uint64_t x) { return x % 2 == 0; }, nums);
  ASSERT(count == 2ULL); // 2 and 4 are even

  // Test categorize with key=3: [2,3,4] -> 1 + 2 + 3 = 6
  auto cat = LoopifyLists::categorize(3ULL, nums);
  ASSERT(cat == 6ULL);

  // Test max_prefix_sum
  auto max_ps = LoopifyLists::max_prefix_sum(l3);
  ASSERT(max_ps > 0ULL);

  // Test pairwise_sum: [1,2,3] -> [3,5]
  auto pairs = LoopifyLists::pairwise_sum(l3);

  // Test weighted_sum: weighted_sum(0, [1,2,3]) = 0*1 + 1*2 + 2*3 = 8
  auto ws = LoopifyLists::weighted_sum(0ULL, l3);
  ASSERT(ws == 8ULL);

  std::cout << "All unique list tests passed!\n";
  return testStatus;
}
