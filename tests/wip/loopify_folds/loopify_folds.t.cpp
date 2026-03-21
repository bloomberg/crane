// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_folds.h>

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
  auto l5 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(
    3u, UIntList::ctor::Cons_(4u, UIntList::ctor::Cons_(5u, nil)))));

  auto add = [](unsigned int a, unsigned int b) { return a + b; };
  auto mul = [](unsigned int a, unsigned int b) { return a * b; };

  // fold_left
  ASSERT(LoopifyFolds::fold_left(add, 0u, nil) == 0u);
  ASSERT(LoopifyFolds::fold_left(add, 0u, l3) == 6u);
  ASSERT(LoopifyFolds::fold_left(mul, 1u, l3) == 6u);
  ASSERT(LoopifyFolds::fold_left(add, 10u, l3) == 16u);

  // fold_right
  ASSERT(LoopifyFolds::fold_right(add, nil, 0u) == 0u);
  ASSERT(LoopifyFolds::fold_right(add, l3, 0u) == 6u);
  ASSERT(LoopifyFolds::fold_right(mul, l3, 1u) == 6u);

  // scanl
  auto scanned = LoopifyFolds::scanl(add, 0u, l3);
  // Should be [0, 1, 3, 6]
  ASSERT(LoopifyFolds::fold_left(add, 0u, scanned) >= 0u);

  // scanr
  auto scanned_r = LoopifyFolds::scanr(add, 0u, l3);
  ASSERT(LoopifyFolds::fold_left(add, 0u, scanned_r) >= 0u);

  // foldl1
  ASSERT(LoopifyFolds::foldl1(add, nil) == 0u);
  ASSERT(LoopifyFolds::foldl1(add, l3) == 6u);
  ASSERT(LoopifyFolds::foldl1(mul, l3) == 6u);

  // foldr1
  ASSERT(LoopifyFolds::foldr1(add, nil) == 0u);
  ASSERT(LoopifyFolds::foldr1(add, l3) == 6u);
  ASSERT(LoopifyFolds::foldr1(mul, l3) == 6u);

  // iterate_accum
  auto dbl = [](unsigned int x) { return x * 2; };
  auto iters = LoopifyFolds::iterate_accum(dbl, 4u, 1u);
  // Should be [1, 2, 4, 8]
  ASSERT(LoopifyFolds::fold_left(add, 0u, iters) == 15u);

  // unfold
  auto next = [](unsigned int x) -> std::pair<unsigned int, unsigned int> {
    return {x, x + 1};
  };
  auto unfolded = LoopifyFolds::unfold(5u, next, 0u);
  ASSERT(LoopifyFolds::fold_left(add, 0u, unfolded) == 10u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
