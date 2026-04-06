#ifndef INCLUDED_Z_ABS_MIN
#define INCLUDED_Z_ABS_MIN

#include <cstdint>
#include <cstdlib>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct BinInt {};

struct ZAbsMin {
  /// In Rocq, Z.abs is total: Z.abs z is always non-negative.
  /// ZInt maps Z.abs to std::abs(%a0) (from <cstdlib>).
  /// But std::abs(INT64_MIN) is undefined behavior in C++
  /// because -INT64_MIN cannot be represented as int64_t.
  __attribute__((pure)) static int64_t my_abs(const int64_t _x0);
  /// Construct INT64_MIN = -2^63 via INT64_MAX + 1 negated.
  static inline const int64_t neg_max = (-INT64_C(9223372036854775807));
  static inline const int64_t int64_min = (neg_max - 1);
  /// In Rocq, this is 9223372036854775808 (positive).
  /// In C++, std::abs(INT64_MIN) is UB — typically returns INT64_MIN.
  static inline const int64_t abs_of_min = std::abs(int64_min);
  /// Should always be true for Z.abs, but fails in C++.
  __attribute__((pure)) static bool is_nonneg(const int64_t x);
};

#endif // INCLUDED_Z_ABS_MIN
