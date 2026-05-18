#ifndef INCLUDED_INT63_ARITH
#define INCLUDED_INT63_ARITH

#include <cstdint>

struct Int63Arith {
  static inline const int64_t i_zero = INT64_C(0);
  static inline const int64_t i_one = INT64_C(1);
  static inline const int64_t i_add =
      ((INT64_C(10) + INT64_C(20)) & 0x7FFFFFFFFFFFFFFFLL);
  static inline const int64_t i_mul =
      ((INT64_C(6) * INT64_C(7)) & 0x7FFFFFFFFFFFFFFFLL);
  static inline const int64_t i_sub =
      ((INT64_C(50) - INT64_C(8)) & 0x7FFFFFFFFFFFFFFFLL);
  static inline const bool i_eqb_true = INT64_C(42) == INT64_C(42);
  static inline const bool i_eqb_false = INT64_C(42) == INT64_C(43);
  static inline const bool i_ltb_true = INT64_C(3) < INT64_C(5);
  static inline const bool i_ltb_false = INT64_C(5) < INT64_C(3);
  static inline const bool i_leb_true = INT64_C(3) <= INT64_C(3);
  static inline const bool i_leb_false = INT64_C(5) <= INT64_C(3);
  static int64_t i_abs(int64_t x);
  static inline const int64_t test_abs_pos = i_abs(INT64_C(42));
  static inline const int64_t test_abs_neg =
      i_abs(((INT64_C(0) - INT64_C(42)) & 0x7FFFFFFFFFFFFFFFLL));
};

#endif // INCLUDED_INT63_ARITH
