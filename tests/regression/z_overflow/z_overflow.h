#ifndef INCLUDED_Z_OVERFLOW
#define INCLUDED_Z_OVERFLOW

#include <cstdint>

struct ZOverflow {
  /// 10 billion: fits in int64_t but not unsigned int
  static inline const int64_t big_z = INT64_C(9999999999);
  /// negative 10 billion
  static inline const int64_t big_neg_z = INT64_C(-9999999999);
  /// 2^33: just over unsigned int range
  static inline const int64_t z_pow2_33 = INT64_C(8589934592);
  /// Z value that fits in unsigned int (should work)
  static inline const int64_t z_fits = INT64_C(1000000000);
  /// Nat > 2^32 also overflows unsigned int
  static inline const uint64_t big_nat = UINT64_C(4294967296);
};

#endif // INCLUDED_Z_OVERFLOW
