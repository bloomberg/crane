#ifndef INCLUDED_SIGMA_ASSERT
#define INCLUDED_SIGMA_ASSERT

#include <cassert>
#include <memory>
#include <optional>
#include <type_traits>

struct PeanoNat {
  static unsigned int div2(const unsigned int n);
};

struct SigmaAssert {
  static unsigned int safe_pred(const unsigned int &n);
  static unsigned int safe_div2(const unsigned int &n);
  static inline const unsigned int test_pred = safe_pred(5u);
  static inline const unsigned int test_div2 = safe_div2(4u);
};

#endif // INCLUDED_SIGMA_ASSERT
