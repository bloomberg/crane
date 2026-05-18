#ifndef INCLUDED_ANON_FIXPOINT
#define INCLUDED_ANON_FIXPOINT

#include <utility>

struct AnonFixpoint {
  static uint64_t sum_to(uint64_t n);
  static uint64_t factorial(uint64_t m);
  static uint64_t double_sum(uint64_t m);
  static uint64_t gcd(uint64_t a, uint64_t b);
  static uint64_t test_shadow(uint64_t n);
  static inline const uint64_t test_sum_5 = sum_to(UINT64_C(5));
  static inline const uint64_t test_sum_0 = sum_to(UINT64_C(0));
  static inline const uint64_t test_fact_5 = factorial(UINT64_C(5));
  static inline const uint64_t test_fact_0 = factorial(UINT64_C(0));
  static inline const uint64_t test_double = double_sum(UINT64_C(3));
  static inline const uint64_t test_gcd =
      gcd((UINT64_C(4) * UINT64_C(3)), (UINT64_C(2) * UINT64_C(3)));
};

#endif // INCLUDED_ANON_FIXPOINT
