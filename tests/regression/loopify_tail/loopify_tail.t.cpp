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
  using List = LoopifyTail::list<unsigned int>;

  // Build a small list: [1, 2, 3]
  auto small = List::ctor::Cons_(
      1u, List::ctor::Cons_(2u, List::ctor::Cons_(3u, List::ctor::Nil_())));

  // Test last
  ASSERT(LoopifyTail::last(0u, small) == 3u);

  // Test length
  ASSERT(LoopifyTail::length(small) == 3u);

  // Test member
  ASSERT(LoopifyTail::member(2u, small) == true);
  ASSERT(LoopifyTail::member(5u, small) == false);

  // Test nth
  ASSERT(LoopifyTail::nth(0u, small, 99u) == 1u);
  ASSERT(LoopifyTail::nth(2u, small, 99u) == 3u);
  ASSERT(LoopifyTail::nth(5u, small, 99u) == 99u);

  // Test fold_left (sum)
  auto sum_fn = [](unsigned int acc, unsigned int x) -> unsigned int {
    return acc + x;
  };
  ASSERT(LoopifyTail::fold_left(sum_fn, 0u, small) == 6u);

  // Test lookup
  using PList = LoopifyTail::list<std::pair<unsigned int, unsigned int>>;
  auto assoc = PList::ctor::Cons_(
      std::make_pair(1u, 10u),
      PList::ctor::Cons_(
          std::make_pair(2u, 20u),
          PList::ctor::Cons_(std::make_pair(3u, 30u), PList::ctor::Nil_())));
  ASSERT(LoopifyTail::lookup(2u, assoc) == 20u);
  ASSERT(LoopifyTail::lookup(5u, assoc) == 0u);

  // Build a moderately large list to test no stack overflow
  auto big = List::ctor::Nil_();
  for (unsigned int i = 0; i < 10000; ++i) {
    big = List::ctor::Cons_(i, big);
  }

  // These use the loopified (iterative) versions - should not stack overflow
  ASSERT(LoopifyTail::last(0u, big) == 0u);
  ASSERT(LoopifyTail::length(big) == 10000u);
  ASSERT(LoopifyTail::member(5000u, big) == true);
  ASSERT(LoopifyTail::fold_left(sum_fn, 0u, big) == 49995000u);

  // Iteratively destroy the big list to avoid shared_ptr destructor
  // stack overflow (a known limitation of shared_ptr for deep lists)
  while (std::holds_alternative<List::Cons>(big->v_mut())) {
    auto next = std::get<List::Cons>(big->v_mut()).d_a1;
    big = next;
  }
  big.reset();

  return testStatus;
}
