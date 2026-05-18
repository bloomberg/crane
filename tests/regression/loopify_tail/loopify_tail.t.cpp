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
      UINT64_C(1), List::cons(UINT64_C(2), List::cons(UINT64_C(3), List::nil())));

  // Test last
  ASSERT(LoopifyTail::last(UINT64_C(0), small) == UINT64_C(3));

  // Test length
  ASSERT(LoopifyTail::length(small) == UINT64_C(3));

  // Test member
  ASSERT(LoopifyTail::member(UINT64_C(2), small) == true);
  ASSERT(LoopifyTail::member(UINT64_C(5), small) == false);

  // Test nth
  ASSERT(LoopifyTail::nth(UINT64_C(0), small, UINT64_C(99)) == UINT64_C(1));
  ASSERT(LoopifyTail::nth(UINT64_C(2), small, UINT64_C(99)) == UINT64_C(3));
  ASSERT(LoopifyTail::nth(UINT64_C(5), small, UINT64_C(99)) == UINT64_C(99));

  // Test fold_left (sum)
  auto sum_fn = [](uint64_t acc, uint64_t x) -> unsigned int {
    return acc + x;
  };
  ASSERT(LoopifyTail::fold_left(sum_fn, UINT64_C(0), small) == UINT64_C(6));

  // Test lookup
  using PList = LoopifyTail::list<std::pair<uint64_t, uint64_t>>;
  auto assoc = PList::cons(
      std::make_pair(UINT64_C(1), UINT64_C(10)),
      PList::cons(
          std::make_pair(UINT64_C(2), UINT64_C(20)),
          PList::cons(std::make_pair(UINT64_C(3), UINT64_C(30)), PList::nil())));
  ASSERT(LoopifyTail::lookup(UINT64_C(2), assoc) == UINT64_C(20));
  ASSERT(LoopifyTail::lookup(UINT64_C(5), assoc) == UINT64_C(0));

  // Build a moderately large list to test no stack overflow
  auto big = List::nil();
  for (unsigned int i = 0; i < 10000; ++i) {
    big = List::cons(i, std::move(big));
  }

  // These use the loopified (iterative) versions - should not stack overflow
  ASSERT(LoopifyTail::last(UINT64_C(0), big) == UINT64_C(0));
  ASSERT(LoopifyTail::length(big) == UINT64_C(10000));
  ASSERT(LoopifyTail::member(UINT64_C(5000), big) == true);
  ASSERT(LoopifyTail::fold_left(sum_fn, UINT64_C(0), big) == UINT64_C(49995000));

  // Iteratively destroy the big list to avoid destructor
  // stack overflow (a known limitation for deep lists)
  while (std::holds_alternative<List::Cons>(big.v_mut())) {
    auto next = std::move(std::get<List::Cons>(big.v_mut()).l);
    big = std::move(*next);
  }

  return testStatus;
}
