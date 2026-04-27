#ifndef INCLUDED_ANON_FIXPOINT
#define INCLUDED_ANON_FIXPOINT

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct AnonFixpoint {
  __attribute__((pure)) static unsigned int sum_to(const unsigned int &n);
  __attribute__((pure)) static unsigned int factorial(const unsigned int &m);
  __attribute__((pure)) static unsigned int double_sum(const unsigned int &m);
  __attribute__((pure)) static unsigned int gcd(const unsigned int &a,
                                                const unsigned int &b);
  __attribute__((pure)) static unsigned int test_shadow(const unsigned int &n);
  static inline const unsigned int test_sum_5 = sum_to(5u);
  static inline const unsigned int test_sum_0 = sum_to(0u);
  static inline const unsigned int test_fact_5 = factorial(5u);
  static inline const unsigned int test_fact_0 = factorial(0u);
  static inline const unsigned int test_double = double_sum(3u);
  static inline const unsigned int test_gcd = gcd((4u * 3u), (2u * 3u));
};

#endif // INCLUDED_ANON_FIXPOINT
