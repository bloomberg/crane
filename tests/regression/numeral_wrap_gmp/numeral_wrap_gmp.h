#ifndef INCLUDED_NUMERAL_WRAP_GMP
#define INCLUDED_NUMERAL_WRAP_GMP

#include <gmpxx.h>

struct NumeralWrapGmp {
  static inline const mpz_class two62 = (4611686018427387904_mpz);
  static inline const mpz_class two63 = (9223372036854775808_mpz);
  static inline const mpz_class two64 = (18446744073709551616_mpz);
  static inline const mpz_class two64_1 = (18446744073709551617_mpz);
  static inline const mpz_class two128 =
      (340282366920938463463374607431768211456_mpz);

  static inline const mpz_class neg64 = (-18446744073709551616_mpz);
};

#endif // INCLUDED_NUMERAL_WRAP_GMP
