#ifndef INCLUDED_LOOPIFY_CLASSICS
#define INCLUDED_LOOPIFY_CLASSICS

#include <utility>
#include <variant>
#include <vector>

struct LoopifyClassics {
  static unsigned int factorial(unsigned int n);
  static unsigned int fib(unsigned int n);
  static unsigned int ack_fuel(unsigned int fuel, unsigned int m,
                               unsigned int n);
  static unsigned int ack(unsigned int m, unsigned int n);
  static unsigned int binomial_fuel(unsigned int fuel, unsigned int n,
                                    unsigned int k);
  static unsigned int binomial(unsigned int n, unsigned int k);
  static unsigned int pascal_fuel(unsigned int fuel, unsigned int row,
                                  unsigned int col);
  static unsigned int pascal(unsigned int row, unsigned int col);
  static unsigned int gcd_fuel(unsigned int fuel, unsigned int a,
                               unsigned int b);
  static unsigned int gcd(unsigned int a, unsigned int b);
  static unsigned int power(unsigned int base, unsigned int exp);
  static unsigned int sum_to(unsigned int n);
  static unsigned int sum_squares(unsigned int n);
};

#endif // INCLUDED_LOOPIFY_CLASSICS
