#ifndef INCLUDED_Z_ABS_MIN
#define INCLUDED_Z_ABS_MIN

#include <cstdint>

struct ZAbsMin {
  /// In Rocq, Z.abs is total: Z.abs z is always non-negative.
  /// ZInt maps Z.abs to std::abs(%a0) (from <cstdlib>).
  /// But std::abs(INT64_MIN) is undefined behavior in C++
  /// because -INT64_MIN cannot be represented as int64_t.
  static int64_t my_abs(int64_t _x0);
  /// Construct INT64_MIN = -2^63 via INT64_MAX + 1 negated.
  static inline const int64_t neg_max = static_cast<int64_t>(
      -static_cast<uint64_t>(INT64_C(9223372036854775807)));

  static inline const int64_t int64_min =
      static_cast<int64_t>(static_cast<uint64_t>(neg_max) - 1);
  /// In Rocq, this is 9223372036854775808 (positive).
  /// In C++, std::abs(INT64_MIN) is UB — typically returns INT64_MIN.
  static inline const int64_t abs_of_min =
      (int64_min < 0 ? static_cast<int64_t>(-static_cast<uint64_t>(int64_min))
                     : int64_min);
  /// Should always be true for Z.abs, but fails in C++.
  static bool is_nonneg(int64_t x);
};

#endif // INCLUDED_Z_ABS_MIN
