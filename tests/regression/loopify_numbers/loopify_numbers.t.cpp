// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_numbers.h>

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
  // Test unique number functions
  ASSERT(LoopifyNumbers::factorial(5u) == 120u);
  ASSERT(LoopifyNumbers::fib(7u) == 13u);
  ASSERT(LoopifyNumbers::gcd(48u, 18u) == 6u);
  ASSERT(LoopifyNumbers::binomial(5u, 2u) == 10u);
  ASSERT(LoopifyNumbers::tribonacci(4u) == 2u);
  ASSERT(LoopifyNumbers::digitsum(123u) == 6u);
  ASSERT(LoopifyNumbers::ack(1u, 2u) == 4u);
  ASSERT(LoopifyNumbers::sum_to(5u) == 15u);
  ASSERT(LoopifyNumbers::sum_squares(3u) == 14u); // 1 + 4 + 9
  ASSERT(LoopifyNumbers::staircase(4u) > 0u);
  ASSERT(LoopifyNumbers::dec_to_bin(5u) == 101u);

  std::cout << "All unique number tests passed!\n";
  return testStatus;
}
