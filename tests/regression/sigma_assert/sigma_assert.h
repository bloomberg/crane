#ifndef INCLUDED_SIGMA_ASSERT
#define INCLUDED_SIGMA_ASSERT

#include <cassert>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct PeanoNat {
  __attribute__((pure)) static unsigned int div2(const unsigned int n);
};

struct SigmaAssert {
  __attribute__((pure)) static unsigned int safe_pred(const unsigned int n);
  __attribute__((pure)) static unsigned int safe_div2(const unsigned int n);
  static inline const unsigned int test_pred = safe_pred(5u);
  static inline const unsigned int test_div2 = safe_div2(4u);
};

#endif // INCLUDED_SIGMA_ASSERT
