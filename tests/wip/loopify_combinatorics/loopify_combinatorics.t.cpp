// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_combinatorics.h>

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
  using List = ::List<unsigned int>;

  // Test remove
  auto l = List::ctor::Cons_(
      1u, List::ctor::Cons_(2u, List::ctor::Cons_(3u, List::ctor::Nil_())));
  auto removed = LoopifyCombinatorics::remove(2u, l);
  ASSERT(removed != nullptr);

  // Test permutations (small list)
  auto small = List::ctor::Cons_(1u, List::ctor::Cons_(2u, List::ctor::Nil_()));
  auto perms = LoopifyCombinatorics::permutations(small);
  ASSERT(perms != nullptr);

  // Test subsequences
  auto subseqs = LoopifyCombinatorics::subsequences(l);
  ASSERT(subseqs != nullptr);

  // Test cartesian
  auto l1 = List::ctor::Cons_(1u, List::ctor::Cons_(2u, List::ctor::Nil_()));
  auto l2 = List::ctor::Cons_(3u, List::ctor::Cons_(4u, List::ctor::Nil_()));
  auto cart = LoopifyCombinatorics::cartesian(l1, l2);
  ASSERT(cart != nullptr);

  // Test power_set
  auto pset = LoopifyCombinatorics::power_set(small);
  ASSERT(pset != nullptr);

  // Test insert_everywhere
  auto inserted = LoopifyCombinatorics::insert_everywhere(5u, small);
  ASSERT(inserted != nullptr);

  std::cout << "All combinatorics tests passed!\n";
  return testStatus;
}
