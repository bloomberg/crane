// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_tail.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  using List = LoopifyTail::list<uint64_t>;

  // Build a small list: [1, 2, 3]
  auto small = List::cons(
      1ULL, List::cons(2ULL, List::cons(3ULL, List::nil())));

  // Test last
  ASSERT(LoopifyTail::last(0ULL, small) == 3ULL);

  // Test length
  ASSERT(LoopifyTail::length(small) == 3ULL);

  // Test member
  ASSERT(LoopifyTail::member(2ULL, small) == true);
  ASSERT(LoopifyTail::member(5ULL, small) == false);

  // Test nth
  ASSERT(LoopifyTail::nth(0ULL, small, 99ULL) == 1ULL);
  ASSERT(LoopifyTail::nth(2ULL, small, 99ULL) == 3ULL);
  ASSERT(LoopifyTail::nth(5ULL, small, 99ULL) == 99ULL);

  // Test fold_left (sum)
  auto sum_fn = [](uint64_t acc, uint64_t x) -> unsigned int {
    return acc + x;
  };
  ASSERT(LoopifyTail::fold_left(sum_fn, 0ULL, small) == 6ULL);

  // Test lookup
  using PList = LoopifyTail::list<std::pair<uint64_t, uint64_t>>;
  auto assoc = PList::cons(
      std::make_pair(1ULL, 10ULL),
      PList::cons(
          std::make_pair(2ULL, 20ULL),
          PList::cons(std::make_pair(3ULL, 30ULL), PList::nil())));
  ASSERT(LoopifyTail::lookup(2ULL, assoc) == 20ULL);
  ASSERT(LoopifyTail::lookup(5ULL, assoc) == 0ULL);

  // Build a moderately large list to test no stack overflow
  auto big = List::nil();
  for (unsigned int i = 0; i < 10000; ++i) {
    big = List::cons(i, std::move(big));
  }

  // These use the loopified (iterative) versions - should not stack overflow
  ASSERT(LoopifyTail::last(0ULL, big) == 0ULL);
  ASSERT(LoopifyTail::length(big) == 10000ULL);
  ASSERT(LoopifyTail::member(5000ULL, big) == true);
  ASSERT(LoopifyTail::fold_left(sum_fn, 0ULL, big) == 49995000ULL);

  // Iteratively destroy the big list to avoid destructor
  // stack overflow (a known limitation for deep lists)
  while (std::holds_alternative<List::Cons>(big.v_mut())) {
    auto next = std::move(std::get<List::Cons>(big.v_mut()).a1);
    big = std::move(*next);
  }

  return testStatus;
}
