#include <sigma_assert.h>

#include <cassert>
#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) unsigned int PeanoNat::div2(const unsigned int &n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0u;
    } else {
      unsigned int n_ = n0 - 1;
      return (PeanoNat::div2(n_) + 1);
    }
  }
}

__attribute__((pure)) unsigned int
SigmaAssert::safe_pred(const unsigned int &n) { // Precondition: n != 0
  assert(n != 0);
  return (n ? n - 1 : n);
}

__attribute__((pure)) unsigned int
SigmaAssert::safe_div2(const unsigned int &n) { // Precondition: n >= 1
  assert(n >= 1);
  return PeanoNat::div2(n);
}
