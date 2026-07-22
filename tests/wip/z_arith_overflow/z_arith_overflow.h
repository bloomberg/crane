#ifndef INCLUDED_Z_ARITH_OVERFLOW
#define INCLUDED_Z_ARITH_OVERFLOW

#include <cstdint>

struct ZArithOverflow {
  /// Compute 3,100,000,000 via nat -> Z conversion.
  /// 3,100,000,000 fits in unsigned int (< 2^32) and int64_t.
  static inline const int64_t big_z =
      static_cast<int64_t>(UINT64_C(3100000000));
  /// 3,100,000,000^2 = 9,610,000,000,000,000,000 > INT64_MAX.
  /// In Rocq: perfectly fine (Z is arbitrary precision).
  /// In C++: signed integer multiplication overflow — UB.
  static inline const int64_t overflow_mul = static_cast<int64_t>(
      static_cast<uint64_t>(big_z) * static_cast<uint64_t>(big_z));
  /// The result should be positive (product of two positives).
  /// In C++ the overflowed result wraps to a negative value.
  static inline const bool is_positive = INT64_C(0) < overflow_mul;
  /// Addition near INT64_MAX
  static inline const int64_t near_max =
      static_cast<int64_t>(UINT64_C(4000000000));
  static inline const int64_t near_max_sq = static_cast<int64_t>(
      static_cast<uint64_t>(near_max) * static_cast<uint64_t>(near_max));
  /// Negation of the most negative int64_t is also UB
  static inline const int64_t neg_big = static_cast<int64_t>(
      -static_cast<uint64_t>(static_cast<int64_t>(UINT64_C(4000000000))));

  static inline const int64_t neg_sq = static_cast<int64_t>(
      static_cast<uint64_t>(neg_big) * static_cast<uint64_t>(neg_big));
};

#endif // INCLUDED_Z_ARITH_OVERFLOW
