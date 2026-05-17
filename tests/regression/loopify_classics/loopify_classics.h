#ifndef INCLUDED_LOOPIFY_CLASSICS
#define INCLUDED_LOOPIFY_CLASSICS

#include <utility>
#include <variant>
#include <vector>

struct LoopifyClassics {
  static uint64_t factorial(uint64_t n);
  static uint64_t fib(uint64_t n);
  static uint64_t ack_fuel(uint64_t fuel, uint64_t m, uint64_t n);
  static uint64_t ack(uint64_t m, uint64_t n);
  static uint64_t binomial_fuel(uint64_t fuel, uint64_t n, uint64_t k);
  static uint64_t binomial(uint64_t n, uint64_t k);
  static uint64_t pascal_fuel(uint64_t fuel, uint64_t row, uint64_t col);
  static uint64_t pascal(uint64_t row, uint64_t col);
  static uint64_t gcd_fuel(uint64_t fuel, uint64_t a, uint64_t b);
  static uint64_t gcd(uint64_t a, uint64_t b);
  static uint64_t power(uint64_t base, uint64_t exp);
  static uint64_t sum_to(uint64_t n);
  static uint64_t sum_squares(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_CLASSICS
