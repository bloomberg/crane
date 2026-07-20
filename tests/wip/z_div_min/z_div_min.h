#ifndef INCLUDED_Z_DIV_MIN
#define INCLUDED_Z_DIV_MIN

#include <cstdint>
#include <utility>

struct ZDivMin {
  /// Build INT64_MIN = -9223372036854775808 via Z.opp(Z.of_nat ...)
  static inline const int64_t neg_max = static_cast<int64_t>(
      -static_cast<uint64_t>(INT64_C(9223372036854775807)));
  static inline const int64_t int64_min =
      static_cast<int64_t>(static_cast<uint64_t>(neg_max) - 1);
  /// INT64_MIN / -1 = 9223372036854775808, which doesn't fit in int64_t.
  /// In Rocq: perfectly fine, result is positive.
  /// In C++: signed division overflow → undefined behavior.
  static inline const int64_t div_min_neg1 = [&]() -> int64_t {
    int64_t _a = int64_min;
    int64_t _b = INT64_C(-1);
    if (_b == 0)
      return INT64_C(0);
    if (_b == -1)
      return static_cast<int64_t>(-static_cast<uint64_t>(_a));
    int64_t _q = _a / _b;
    int64_t _r = _a % _b;
    if (_r != 0 && ((_r < 0) != (_b < 0)))
      return _q - 1;
    return _q;
  }();
  /// The result should be positive (dividing negative by negative).
  static inline const bool div_is_positive = INT64_C(0) < div_min_neg1;
  /// INT64_MIN % -1 = 0 in Rocq.
  /// In C++: also UB (same overflow issue).
  static inline const int64_t mod_min_neg1 = [&]() -> int64_t {
    int64_t _a = int64_min;
    int64_t _b = INT64_C(-1);
    if (_b == 0)
      return _a;
    if (_b == -1)
      return INT64_C(0);
    int64_t _r = _a % _b;
    if (_r != 0 && ((_r < 0) != (_b < 0)))
      return _r + _b;
    return _r;
  }();
  /// Z.opp INT64_MIN is also UB: -(INT64_MIN) overflows int64_t.
  /// In Rocq: result is positive 9223372036854775808.
  static inline const int64_t opp_min =
      static_cast<int64_t>(-static_cast<uint64_t>(int64_min));

  static inline const bool opp_is_positive = INT64_C(0) < opp_min;
};

#endif // INCLUDED_Z_DIV_MIN
