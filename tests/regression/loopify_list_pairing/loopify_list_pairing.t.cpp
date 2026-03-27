// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_pairing.h>

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
  auto l5 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    3u, UIntList::cons(4u, UIntList::cons(5u, nil)))));

  // unzip
  using PairList = List<std::pair<unsigned int, unsigned int>>;
  auto pair_nil = PairList::nil();
  auto pairs = PairList::cons(std::make_pair(1u, 10u),
    PairList::cons(std::make_pair(2u, 20u), pair_nil));
  auto unzipped = LoopifyListPairing::unzip(pairs);
  ASSERT(unzipped.first != nullptr && unzipped.second != nullptr);

  // swizzle
  auto swizzled = LoopifyListPairing::swizzle(l5);
  ASSERT(swizzled.first != nullptr && swizzled.second != nullptr);

  // partition
  auto partitioned = LoopifyListPairing::partition(l5);
  ASSERT(partitioned.first != nullptr && partitioned.second != nullptr);

  // zip_longest
  auto l3 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(3u, nil)));
  auto zipped = LoopifyListPairing::zip_longest(l3, l5, 0u);
  ASSERT(zipped != nullptr);

  // zipWith
  auto zw = LoopifyListPairing::zipWith(l3, l3);
  ASSERT(zw != nullptr);

  // split_even_odd
  auto split = LoopifyListPairing::split_even_odd(l5);
  ASSERT(split.first != nullptr && split.second != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
