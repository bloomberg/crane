// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_numeric_sequences.h>

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
  // collatz_length
  ASSERT(LoopifyNumericSequences::collatz_length(1u) == 0u);
  ASSERT(LoopifyNumericSequences::collatz_length(2u) == 1u);
  ASSERT(LoopifyNumericSequences::collatz_length(3u) >= 1u);
  ASSERT(LoopifyNumericSequences::collatz_length(16u) == 4u);

  // collatz_sequence
  auto seq = LoopifyNumericSequences::collatz_sequence(16u);

  // tribonacci
  ASSERT(LoopifyNumericSequences::tribonacci(0u) == 0u);
  ASSERT(LoopifyNumericSequences::tribonacci(1u) == 0u);
  ASSERT(LoopifyNumericSequences::tribonacci(2u) == 1u);
  ASSERT(LoopifyNumericSequences::tribonacci(3u) == 1u);
  ASSERT(LoopifyNumericSequences::tribonacci(4u) == 2u);

  // staircase
  ASSERT(LoopifyNumericSequences::staircase(0u) == 1u);
  ASSERT(LoopifyNumericSequences::staircase(1u) == 1u);
  ASSERT(LoopifyNumericSequences::staircase(3u) >= 1u);

  // church
  auto inc = [](unsigned int x) { return x + 1; };
  ASSERT(LoopifyNumericSequences::church(0u, inc, 5u) == 5u);
  ASSERT(LoopifyNumericSequences::church(3u, inc, 5u) == 8u);

  // digitsum
  ASSERT(LoopifyNumericSequences::digitsum(0u) == 0u);
  ASSERT(LoopifyNumericSequences::digitsum(123u) == 6u);
  ASSERT(LoopifyNumericSequences::digitsum(999u) == 27u);

  // dec_to_bin
  ASSERT(LoopifyNumericSequences::dec_to_bin(0u) == 0u);
  ASSERT(LoopifyNumericSequences::dec_to_bin(5u) == 101u);
  ASSERT(LoopifyNumericSequences::dec_to_bin(8u) == 1000u);

  // sum_divisors
  ASSERT(LoopifyNumericSequences::sum_divisors(1u) == 0u);
  ASSERT(LoopifyNumericSequences::sum_divisors(6u) == 6u);  // 1+2+3
  ASSERT(LoopifyNumericSequences::sum_divisors(12u) == 16u); // 1+2+3+4+6

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
