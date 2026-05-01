// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_transforms.h>

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
  auto l_dups = UIntList::cons(1u, UIntList::cons(1u, UIntList::cons(
    2u, UIntList::cons(2u, UIntList::cons(3u, nil)))));

  // run_length_encode
  auto rle = LoopifyListTransforms::run_length_encode(l_dups);

  // prefix_sums
  auto ps = LoopifyListTransforms::prefix_sums(0u, l5);

  // sliding_pairs
  auto pairs = LoopifyListTransforms::sliding_pairs(l5);

  // differences
  auto diffs = LoopifyListTransforms::differences(l5);

  // take
  auto taken = LoopifyListTransforms::take(3u, l5);

  // drop
  auto dropped = LoopifyListTransforms::drop(2u, l5);

  // chunks_of
  auto chunks = LoopifyListTransforms::chunks_of(2u, l5);

  // rotate_left
  auto rotated = LoopifyListTransforms::rotate_left(2u, l5);

  // uniq_sorted
  auto uniq = LoopifyListTransforms::uniq_sorted(l_dups);

  // step_sum
  ASSERT(LoopifyListTransforms::step_sum(l5) > 0u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
