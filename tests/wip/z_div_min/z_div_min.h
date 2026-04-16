#ifndef INCLUDED_Z_DIV_MIN
#define INCLUDED_Z_DIV_MIN

#include <cstdint>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ZDivMin {
  /// Build INT64_MIN = -9223372036854775808 via Z.opp(Z.of_nat ...)
  static inline const int64_t neg_max = (-INT64_C(9223372036854775807));
  static inline const int64_t int64_min = (neg_max - 1);
  /// INT64_MIN / -1 = 9223372036854775808, which doesn't fit in int64_t.
  /// In Rocq: perfectly fine, result is positive.
  /// In C++: signed division overflow → undefined behavior.
  static inline const int64_t div_min_neg1 =
      (INT64_C(-1) == 0 ? INT64_C(0) : int64_min / INT64_C(-1));
  /// The result should be positive (dividing negative by negative).
  static inline const bool div_is_positive = INT64_C(0) < div_min_neg1;
  /// INT64_MIN % -1 = 0 in Rocq.
  /// In C++: also UB (same overflow issue).
  static inline const int64_t mod_min_neg1 =
      (INT64_C(-1) == 0 ? INT64_C(0) : int64_min % INT64_C(-1));
  /// Z.opp INT64_MIN is also UB: -(INT64_MIN) overflows int64_t.
  /// In Rocq: result is positive 9223372036854775808.
  static inline const int64_t opp_min = (-int64_min);
  static inline const bool opp_is_positive = INT64_C(0) < opp_min;
};

#endif // INCLUDED_Z_DIV_MIN
