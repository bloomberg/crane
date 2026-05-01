#ifndef INCLUDED_SIGNATURE_PARITY_FIX
#define INCLUDED_SIGNATURE_PARITY_FIX

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

struct SignatureParityFix {
  static unsigned int f(const unsigned int seed);
  static inline const unsigned int t = f(4u);
};

#endif // INCLUDED_SIGNATURE_PARITY_FIX
