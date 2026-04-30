#ifndef INCLUDED_PRIM_FLOAT
#define INCLUDED_PRIM_FLOAT

#include <cmath>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PrimFloat {
  static inline const double f_zero = 0x0p+0;
  static inline const double f_one = 0x1p+0;
  static inline const double f_neg_one = (-0x1p+0);
  static double test_add(const double _x0, const double _x1);
  static double test_sub(const double _x0, const double _x1);
  static double test_mul(const double _x0, const double _x1);
  static double test_div(const double _x0, const double _x1);
  static double test_opp(const double _x0);
  static double test_abs(const double _x0);
  static double test_sqrt(const double _x0);
  static bool test_eqb(const double _x0, const double _x1);
  static bool test_ltb(const double _x0, const double _x1);
  static bool test_leb(const double _x0, const double _x1);
  static double test_of_uint63(const int64_t _x0);
};

#endif // INCLUDED_PRIM_FLOAT
