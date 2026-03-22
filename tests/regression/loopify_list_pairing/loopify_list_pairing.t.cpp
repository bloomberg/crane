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
  auto nil = UIntList::ctor::Nil_();
  auto l5 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(
    3u, UIntList::ctor::Cons_(4u, UIntList::ctor::Cons_(5u, nil)))));

  // unzip
  using PairList = List<std::pair<unsigned int, unsigned int>>;
  auto pair_nil = PairList::ctor::Nil_();
  auto pairs = PairList::ctor::Cons_(std::make_pair(1u, 10u),
    PairList::ctor::Cons_(std::make_pair(2u, 20u), pair_nil));
  auto unzipped = LoopifyListPairing::unzip(pairs);
  ASSERT(unzipped.first != nullptr && unzipped.second != nullptr);

  // swizzle
  auto swizzled = LoopifyListPairing::swizzle(l5);
  ASSERT(swizzled.first != nullptr && swizzled.second != nullptr);

  // partition
  auto partitioned = LoopifyListPairing::partition(l5);
  ASSERT(partitioned.first != nullptr && partitioned.second != nullptr);

  // zip_longest
  auto l3 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(3u, nil)));
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
