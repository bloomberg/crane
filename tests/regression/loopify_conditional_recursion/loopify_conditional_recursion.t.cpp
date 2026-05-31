// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_conditional_recursion.h>

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

using UIntList = List<uint64_t>;

static UIntList make_large_list(uint64_t n) {
  UIntList l = UIntList::nil();
  for (uint64_t i = n; i > 0; --i)
    l = UIntList::cons(i, std::move(l));
  return l;
}

int main() {
  // --- Small correctness tests ---

  auto nil = UIntList::nil();
  auto l3 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(3u, nil)));
  auto l5 = UIntList::cons(10u, UIntList::cons(20u, UIntList::cons(
      30u, UIntList::cons(40u, UIntList::cons(50u, nil)))));

  // cached_sum with no cache: should recurse to compute
  {
    auto [total, count] = LoopifyConditionalRecursion::cached_sum(
        std::optional<uint64_t>(), l3);
    // l3 = [1,2,3]: cached_sum None [1,2,3]
    //   x=1, sub = cached_sum None [2,3]
    //     x=2, sub = cached_sum None [3]
    //       x=3, sub = cached_sum None [] = (0,0)
    //       => (3+0, 0+1) = (3,1)
    //     => (2+3, 1+1) = (5,2)
    //   => (1+5, 2+1) = (6,3)
    ASSERT(total == 6);
    ASSERT(count == 3);
  }

  // cached_sum with cache: should NOT recurse (use cached value)
  {
    auto [total, count] = LoopifyConditionalRecursion::cached_sum(
        std::make_optional<uint64_t>(99u), l3);
    // l3 = [1,2,3]: cached_sum (Some 99) [1,2,3]
    //   x=1, sub = (99, 0) [cache hit]
    //   => (1+99, 0+1) = (100, 1)
    // NOTE: only processes first element when cache hits
    ASSERT(total == 100);
    ASSERT(count == 1);
  }

  // find_or_recurse
  {
    auto [count, remainder] = LoopifyConditionalRecursion::find_or_recurse(
        30u, l5);
    // l5 = [10,20,30,40,50]: target=30
    //   x=10 != 30, sub = find_or_recurse 30 [20,30,40,50]
    //     x=20 != 30, sub = find_or_recurse 30 [30,40,50]
    //       x=30 == 30, sub = (30, [40,50])
    //       => (30+1, [40,50]) = (31, [40,50])
    //     => (31+1, [40,50]) = (32, [40,50])
    //   => (32+1, [40,50]) = (33, [40,50])
    ASSERT(count == 33);
  }

  // nested_cond
  {
    auto r = LoopifyConditionalRecursion::nested_cond(100u, 5u, 50u, l5);
    // l5 = [10,20,30,40,50], threshold=100, lo=5, hi=50
    //   x=10: 5<=10=T, 10<=50=T => sub=(10,true), result=10+1=11
    // Only processes first element since inner true branch returns immediately
    ASSERT(r == 11);
  }

  // multi_return with no memo
  {
    auto [count, payload] = LoopifyConditionalRecursion::multi_return(
        std::optional<std::pair<uint64_t, uint64_t>>(), l3);
    // l3 = [1,2,3]: multi_return None [1,2,3]
    //   x=1, sub = multi_return None [2,3]
    //     x=2, sub = multi_return None [3]
    //       x=3, sub = multi_return None [] = (0, None)
    //       count=0, payload=None => (0+1, None) = (1, None)
    //     count=1, payload=None => (1+1, None) = (2, None)
    //   count=2, payload=None => (2+1, None) = (3, None)
    ASSERT(count == 3);
    ASSERT(!payload.has_value());
  }

  // multi_return with memo
  {
    auto memo = std::make_optional(std::make_pair(uint64_t(7), uint64_t(8)));
    auto [count, payload] = LoopifyConditionalRecursion::multi_return(
        memo, l3);
    // l3 = [1,2,3]: multi_return (Some (7,8)) [1,2,3]
    //   x=1, sub = (0, Some (7,8)) [memo hit]
    //   count=0, payload=Some(7,8) => (0+1, Some(7+1, 8)) = (1, Some(8,8))
    ASSERT(count == 1);
    ASSERT(payload.has_value());
    ASSERT(payload->first == 8);
    ASSERT(payload->second == 8);
  }

  // accum_with_cache
  {
    auto [total, count] = LoopifyConditionalRecursion::accum_with_cache(3u, l3);
    // l3 = [1,2,3], key=3
    //   x=1: 1!=3, cached=None, sub = accum_with_cache 3 [2,3]
    //     x=2: 2!=3, cached=None, sub = accum_with_cache 3 [3]
    //       x=3: 3==3, cached=Some(6), sub = (6, 0)
    //       => (6+3, 0+1) = (9, 1)
    //     => (9+2, 1+1) = (11, 2)
    //   => (11+1, 2+1) = (12, 3)
    ASSERT(total == 12);
    ASSERT(count == 3);
  }

  // --- Large-scale tests (stack overflow if not loopified) ---

  auto large = make_large_list(200000);

  // cached_sum with no cache on large list (must recurse 200K times)
  {
    auto [total, count] = LoopifyConditionalRecursion::cached_sum(
        std::optional<uint64_t>(), large);
    // Sum of 1..200000 = 200000*200001/2 = 20000100000
    ASSERT(total == 20000100000ull);
    ASSERT(count == 200000);
  }

  // find_or_recurse with target not in list (must recurse 200K times)
  {
    auto [count, remainder] = LoopifyConditionalRecursion::find_or_recurse(
        999999u, large);
    // Target not found: recurses all the way to [], sub=(0,[])
    // Then each step adds 1 to fst sub => count = 200000*(0+1) = 200000
    ASSERT(count == 200000);
  }

  // accum_with_cache with key=0 (never matches, must recurse 200K times)
  {
    auto [total, count] = LoopifyConditionalRecursion::accum_with_cache(
        0u, large);
    ASSERT(total == 20000100000ull);
    ASSERT(count == 200000);
  }

  // multi_return with no memo (must recurse 200K times)
  {
    auto [count, payload] = LoopifyConditionalRecursion::multi_return(
        std::optional<std::pair<uint64_t, uint64_t>>(), large);
    ASSERT(count == 200000);
    ASSERT(!payload.has_value());
  }

  if (testStatus > 0) {
    std::cout << "FAILED (" << testStatus << " assertion(s))" << std::endl;
    return 1;
  }
  std::cout << "All tests passed." << std::endl;
  return testStatus;
}
