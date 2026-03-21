// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_classics.h>

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
  // factorial
  ASSERT(LoopifyClassics::factorial(0u) == 1u);
  ASSERT(LoopifyClassics::factorial(1u) == 1u);
  ASSERT(LoopifyClassics::factorial(5u) == 120u);
  ASSERT(LoopifyClassics::factorial(6u) == 720u);

  // fib
  ASSERT(LoopifyClassics::fib(0u) == 0u);
  ASSERT(LoopifyClassics::fib(1u) == 1u);
  ASSERT(LoopifyClassics::fib(7u) == 13u);
  ASSERT(LoopifyClassics::fib(10u) == 55u);

  // ack - only test small values due to exponential growth
  ASSERT(LoopifyClassics::ack(0u, 0u) == 1u);
  ASSERT(LoopifyClassics::ack(0u, 5u) == 6u);
  ASSERT(LoopifyClassics::ack(1u, 2u) == 4u);
  ASSERT(LoopifyClassics::ack(2u, 2u) == 7u);
  ASSERT(LoopifyClassics::ack(3u, 2u) == 29u);

  // binomial
  ASSERT(LoopifyClassics::binomial(5u, 0u) == 1u);
  ASSERT(LoopifyClassics::binomial(5u, 5u) == 1u);
  ASSERT(LoopifyClassics::binomial(5u, 2u) == 10u);
  ASSERT(LoopifyClassics::binomial(6u, 3u) == 20u);

  // pascal
  ASSERT(LoopifyClassics::pascal(0u, 0u) == 1u);
  ASSERT(LoopifyClassics::pascal(4u, 0u) == 1u);
  ASSERT(LoopifyClassics::pascal(4u, 4u) == 1u);
  ASSERT(LoopifyClassics::pascal(4u, 2u) == 6u);
  ASSERT(LoopifyClassics::pascal(5u, 2u) == 10u);

  // gcd
  ASSERT(LoopifyClassics::gcd(48u, 18u) == 6u);
  ASSERT(LoopifyClassics::gcd(100u, 50u) == 50u);
  ASSERT(LoopifyClassics::gcd(17u, 13u) == 1u);

  // power
  ASSERT(LoopifyClassics::power(2u, 0u) == 1u);
  ASSERT(LoopifyClassics::power(2u, 3u) == 8u);
  ASSERT(LoopifyClassics::power(3u, 4u) == 81u);

  // sum_to
  ASSERT(LoopifyClassics::sum_to(0u) == 0u);
  ASSERT(LoopifyClassics::sum_to(5u) == 15u);
  ASSERT(LoopifyClassics::sum_to(10u) == 55u);

  // sum_squares
  ASSERT(LoopifyClassics::sum_squares(0u) == 0u);
  ASSERT(LoopifyClassics::sum_squares(3u) == 14u);  // 1+4+9
  ASSERT(LoopifyClassics::sum_squares(4u) == 30u);  // 1+4+9+16

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
