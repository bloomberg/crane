#ifndef INCLUDED_PRIM_FLOAT
#define INCLUDED_PRIM_FLOAT

#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct PrimFloat {
  static inline const double f_zero = 0x0p+0;
  static inline const double f_one = 0x1p+0;
  static inline const double f_neg_one = (-0x1p+0);
  __attribute__((pure)) static double test_add(const double _x0,
                                               const double _x1);
  __attribute__((pure)) static double test_sub(const double _x0,
                                               const double _x1);
  __attribute__((pure)) static double test_mul(const double _x0,
                                               const double _x1);
  __attribute__((pure)) static double test_div(const double _x0,
                                               const double _x1);
  __attribute__((pure)) static double test_opp(const double _x0);
  __attribute__((pure)) static double test_abs(const double _x0);
  __attribute__((pure)) static double test_sqrt(const double _x0);
  __attribute__((pure)) static bool test_eqb(const double _x0,
                                             const double _x1);
  __attribute__((pure)) static bool test_ltb(const double _x0,
                                             const double _x1);
  __attribute__((pure)) static bool test_leb(const double _x0,
                                             const double _x1);
  __attribute__((pure)) static double test_of_uint63(const int64_t _x0);
};

#endif // INCLUDED_PRIM_FLOAT
