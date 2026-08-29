#ifndef INCLUDED_Z_OVERFLOW
#define INCLUDED_Z_OVERFLOW

#include <cstdint>

struct ZOverflow {
  static inline const int64_t big_z = INT64_C(9999999999);
  static inline const int64_t big_neg_z = INT64_C(-9999999999);
  static inline const int64_t z_pow2_33 = INT64_C(8589934592);
  static inline const int64_t z_fits = INT64_C(1000000000);
  static inline const uint64_t big_nat = UINT64_C(4294967296);
};

#endif // INCLUDED_Z_OVERFLOW
