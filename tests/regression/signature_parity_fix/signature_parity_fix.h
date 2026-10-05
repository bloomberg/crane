#ifndef INCLUDED_SIGNATURE_PARITY_FIX
#define INCLUDED_SIGNATURE_PARITY_FIX

#include <cstdint>

struct SignatureParityFix {
  static uint64_t f(uint64_t seed);
  static constexpr uint64_t t = UINT64_C(4);
};

#endif // INCLUDED_SIGNATURE_PARITY_FIX
