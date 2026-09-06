#ifndef INCLUDED_PRIM_FLOAT
#define INCLUDED_PRIM_FLOAT

#include <cmath>
#include <cstdint>

struct PrimFloat {
  static inline const double f_zero = 0x0p+0;
  static inline const double f_one = 0x1p+0;
  static inline const double f_neg_one = (-0x1p+0);
  static double test_add(double x0_, double x1_);
  static double test_sub(double x0_, double x1_);
  static double test_mul(double x0_, double x1_);
  static double test_div(double x0_, double x1_);
  static double test_opp(double x0_);
  static double test_abs(double x0_);
  static double test_sqrt(double x0_);
  static bool test_eqb(double x0_, double x1_);
  static bool test_ltb(double x0_, double x1_);
  static bool test_leb(double x0_, double x1_);
  static double test_of_uint63(int64_t x0_);
};

#endif // INCLUDED_PRIM_FLOAT
