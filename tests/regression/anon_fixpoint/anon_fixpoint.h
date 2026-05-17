#ifndef INCLUDED_ANON_FIXPOINT
#define INCLUDED_ANON_FIXPOINT

#include <utility>

struct AnonFixpoint {
  static unsigned int sum_to(unsigned int n);
  static unsigned int factorial(unsigned int m);
  static unsigned int double_sum(unsigned int m);
  static unsigned int gcd(unsigned int a, unsigned int b);
  static unsigned int test_shadow(unsigned int n);
  static inline const unsigned int test_sum_5 = sum_to(5u);
  static inline const unsigned int test_sum_0 = sum_to(0u);
  static inline const unsigned int test_fact_5 = factorial(5u);
  static inline const unsigned int test_fact_0 = factorial(0u);
  static inline const unsigned int test_double = double_sum(3u);
  static inline const unsigned int test_gcd = gcd((4u * 3u), (2u * 3u));
};

#endif // INCLUDED_ANON_FIXPOINT
