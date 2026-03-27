// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_polymorphic.h>

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
  auto l5 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    3u, UIntList::cons(4u, UIntList::cons(5u, nil)))));

  // nat_length
  ASSERT(LoopifyPolymorphic::nat_length(nil) == 0u);
  ASSERT(LoopifyPolymorphic::nat_length(l3) == 3u);
  ASSERT(LoopifyPolymorphic::nat_length(l5) == 5u);

  // nat_reverse
  auto rev = LoopifyPolymorphic::nat_reverse(l3);
  ASSERT(LoopifyPolymorphic::nat_length(rev) == 3u);

  // nat_append
  auto app = LoopifyPolymorphic::nat_append(l3, l3);
  ASSERT(LoopifyPolymorphic::nat_length(app) == 6u);

  // nat_last
  auto last_none = LoopifyPolymorphic::nat_last(nil);
  ASSERT(!last_none);

  auto last_some = LoopifyPolymorphic::nat_last(l3);
  ASSERT(last_some && *last_some == 3u);

  // nat_take
  auto taken = LoopifyPolymorphic::nat_take(2u, l5);
  ASSERT(LoopifyPolymorphic::nat_length(taken) == 2u);

  auto take_zero = LoopifyPolymorphic::nat_take(0u, l3);
  ASSERT(LoopifyPolymorphic::nat_length(take_zero) == 0u);

  // nat_drop
  auto dropped = LoopifyPolymorphic::nat_drop(2u, l5);
  ASSERT(LoopifyPolymorphic::nat_length(dropped) == 3u);

  // nat_nth
  auto nth0 = LoopifyPolymorphic::nat_nth(0u, l3);
  ASSERT(nth0 && *nth0 == 1u);

  auto nth2 = LoopifyPolymorphic::nat_nth(2u, l3);
  ASSERT(nth2 && *nth2 == 3u);

  auto nth_out = LoopifyPolymorphic::nat_nth(10u, l3);
  ASSERT(!nth_out);

  // nat_filter
  auto evens = LoopifyPolymorphic::nat_filter(LoopifyPolymorphic::is_even, l5);
  ASSERT(LoopifyPolymorphic::nat_length(evens) == 2u);  // 2, 4

  // nat_map
  auto doubled = LoopifyPolymorphic::nat_map([](unsigned int x) { return x * 2; }, l3);
  ASSERT(LoopifyPolymorphic::nat_length(doubled) == 3u);

  // nat_partition
  auto parts = LoopifyPolymorphic::nat_partition(LoopifyPolymorphic::is_even, l5);
  ASSERT(LoopifyPolymorphic::nat_length(parts.first) == 2u);  // evens
  ASSERT(LoopifyPolymorphic::nat_length(parts.second) == 3u);  // odds

  // nat_member
  ASSERT(LoopifyPolymorphic::nat_member(2u, l3) == true);
  ASSERT(LoopifyPolymorphic::nat_member(5u, l3) == false);

  // nat_replicate
  auto reps = LoopifyPolymorphic::nat_replicate(4u, 7u);
  ASSERT(LoopifyPolymorphic::nat_length(reps) == 4u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
