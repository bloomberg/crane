#ifndef INCLUDED_Z_INT
#define INCLUDED_Z_INT

#include <cstdint>

struct ZIntTest {
  static int64_t add_test(int64_t x0_, int64_t x1_);
  static int64_t mul_test(int64_t x0_, int64_t x1_);
  static int64_t sub_test(int64_t x0_, int64_t x1_);
  static int64_t abs_test(int64_t x0_);
  static int64_t opp_test(int64_t x0_);
  static bool eqb_test(int64_t x0_, int64_t x1_);
  static bool ltb_test(int64_t x0_, int64_t x1_);
  static bool leb_test(int64_t x0_, int64_t x1_);
  static inline const int64_t zero_val = INT64_C(0);
  static inline const int64_t pos_val = INT64_C(42);
  static inline const int64_t neg_val = INT64_C(-7);
  static inline const int64_t big_val = INT64_C(1000);
  static int64_t z_sign(int64_t z);
};

#endif // INCLUDED_Z_INT
