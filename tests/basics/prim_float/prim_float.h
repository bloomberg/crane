#ifndef INCLUDED_PRIM_FLOAT
#define INCLUDED_PRIM_FLOAT

#include <cmath>
#include <cstdint>

struct PrimFloat {
  static inline const double f_zero = 0x0p+0;
  static inline const double f_one = 0x1p+0;
  static inline const double f_neg_one = (-0x1p+0);
  static double test_add(double _x0, double _x1);
  static double test_sub(double _x0, double _x1);
  static double test_mul(double _x0, double _x1);
  static double test_div(double _x0, double _x1);
  static double test_opp(double _x0);
  static double test_abs(double _x0);
  static double test_sqrt(double _x0);
  static bool test_eqb(double _x0, double _x1);
  static bool test_ltb(double _x0, double _x1);
  static bool test_leb(double _x0, double _x1);
  static double test_of_uint63(int64_t _x0);
};

#endif // INCLUDED_PRIM_FLOAT
