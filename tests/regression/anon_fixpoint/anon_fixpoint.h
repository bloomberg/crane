#ifndef INCLUDED_ANON_FIXPOINT
#define INCLUDED_ANON_FIXPOINT

#include <cstdint>
#include <utility>

struct AnonFixpoint {
  static uint64_t sum_to(uint64_t n);
  static uint64_t factorial(uint64_t m);
  static uint64_t double_sum(uint64_t m);
  static uint64_t gcd(uint64_t a, uint64_t b);
  static uint64_t test_shadow(uint64_t n);
  static constexpr uint64_t test_sum_5 = UINT64_C(15);
  static constexpr uint64_t test_sum_0 = UINT64_C(0);
  static constexpr uint64_t test_fact_5 = UINT64_C(120);
  static constexpr uint64_t test_fact_0 = UINT64_C(1);
  static constexpr uint64_t test_double = UINT64_C(6);
  static constexpr uint64_t test_gcd = UINT64_C(6);
};

#endif // INCLUDED_ANON_FIXPOINT
