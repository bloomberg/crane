#ifndef INCLUDED_SIGNATURE_PARITY_FIX
#define INCLUDED_SIGNATURE_PARITY_FIX

struct SignatureParityFix {
  static unsigned int f(unsigned int seed);
  static inline const unsigned int t = f(4u);
};

#endif // INCLUDED_SIGNATURE_PARITY_FIX
