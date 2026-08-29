#ifndef INCLUDED_SIGNATURE_PARITY_FIX
#define INCLUDED_SIGNATURE_PARITY_FIX

struct SignatureParityFix {
  static uint64_t f(uint64_t seed);
  static inline const uint64_t t = f(UINT64_C(4));
};

#endif // INCLUDED_SIGNATURE_PARITY_FIX
