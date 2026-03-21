// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_generation.h>

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
  // replicate
  auto rep = LoopifyListGeneration::replicate(5u, 42u);
  ASSERT(rep != nullptr);

  // stutter
  auto nil = UIntList::ctor::Nil_();
  auto l3 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(3u, nil)));
  auto stuttered = LoopifyListGeneration::stutter(l3);
  ASSERT(stuttered != nullptr);

  // cycle
  auto cycled = LoopifyListGeneration::cycle(3u, l3);
  ASSERT(cycled != nullptr);

  // iterate
  auto iterated = LoopifyListGeneration::iterate(5u, 10u);
  ASSERT(iterated != nullptr);

  // replicate_list
  using PairList = List<std::pair<unsigned int, unsigned int>>;
  auto pair_nil = PairList::ctor::Nil_();
  auto pairs = PairList::ctor::Cons_(std::make_pair(3u, 5u),
    PairList::ctor::Cons_(std::make_pair(2u, 7u), pair_nil));
  auto rep_list = LoopifyListGeneration::replicate_list(pairs);
  ASSERT(rep_list != nullptr);

  // repeat_with_sep
  auto with_sep = LoopifyListGeneration::repeat_with_sep(0u, 4u, 99u);
  ASSERT(with_sep != nullptr);

  // range
  auto rng = LoopifyListGeneration::range(1u, 10u);
  ASSERT(rng != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
