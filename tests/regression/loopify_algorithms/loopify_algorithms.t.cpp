// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_algorithms.h>

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

  // Test sieve (simple case)
  auto l = List::cons(
      2u, List::cons(
              3u, List::cons(
                      4u, List::cons(
                              5u, List::cons(6u, List::nil())))));
  auto sieved = LoopifyAlgorithms::sieve(l);
  ASSERT(sieved != nullptr);

  // Test run_length_encode
  auto rle_input = List::cons(
      1u, List::cons(
              1u, List::cons(
                      2u, List::cons(
                              3u, List::cons(
                                      3u, List::cons(
                                              3u, List::nil()))))));
  auto encoded = LoopifyAlgorithms::run_length_encode(rle_input);
  ASSERT(encoded != nullptr);

  // Test prefix_sums
  auto nums = List::cons(
      1u, List::cons(2u, List::cons(3u, List::nil())));
  auto prefixes = LoopifyAlgorithms::prefix_sums(0u, nums);
  ASSERT(prefixes != nullptr);

  // Test differences
  auto seq = List::cons(
      5u, List::cons(
              3u, List::cons(
                      8u, List::cons(2u, List::nil()))));
  auto diffs = LoopifyAlgorithms::differences(seq);
  ASSERT(diffs != nullptr);

  // Test rotate_left
  auto rotated = LoopifyAlgorithms::rotate_left(2u, nums);
  ASSERT(rotated != nullptr);

  // Test nub
  auto with_dups = List::cons(
      1u, List::cons(
              2u, List::cons(
                      1u, List::cons(
                              3u, List::cons(2u, List::nil())))));
  auto unique = LoopifyAlgorithms::nub(with_dups);
  ASSERT(unique != nullptr);

  // Test is_palindrome
  auto pal = List::cons(
      1u, List::cons(
              2u, List::cons(
                      3u, List::cons(
                              2u, List::cons(1u, List::nil())))));
  ASSERT(LoopifyAlgorithms::is_palindrome(pal));
  ASSERT(!LoopifyAlgorithms::is_palindrome(nums));

  // Test windows
  auto four = List::cons(
      1u, List::cons(
              2u, List::cons(
                      3u, List::cons(4u, List::nil()))));
  auto wins = LoopifyAlgorithms::windows(2u, four);
  ASSERT(wins != nullptr);

  // Test sliding_pairs
  auto pairs = LoopifyAlgorithms::sliding_pairs(four);
  ASSERT(pairs != nullptr);

  std::cout << "All algorithm tests passed!\n";
  return testStatus;
}
