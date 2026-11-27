#pragma once

#include <cstdint>

struct Int63Arith {
  static constexpr int64_t i_zero = INT64_C(0);
  static constexpr int64_t i_one = INT64_C(1);
  static inline const int64_t i_add = static_cast<int64_t>(
      (UINT64_C(10) + UINT64_C(20)) & UINT64_C(9223372036854775807));
  static inline const int64_t i_mul = static_cast<int64_t>(
      (UINT64_C(6) * UINT64_C(7)) & UINT64_C(9223372036854775807));
  static inline const int64_t i_sub = static_cast<int64_t>(
      (UINT64_C(50) - UINT64_C(8)) & UINT64_C(9223372036854775807));
  static constexpr bool i_eqb_true = true;
  static inline const bool i_eqb_false = INT64_C(42) == INT64_C(43);
  static inline const bool i_ltb_true = INT64_C(3) < INT64_C(5);
  static inline const bool i_ltb_false = INT64_C(5) < INT64_C(3);
  static constexpr bool i_leb_true = true;
  static inline const bool i_leb_false = INT64_C(5) <= INT64_C(3);
  static int64_t i_abs(int64_t x);
  static inline const int64_t test_abs_pos = i_abs(INT64_C(42));
  static inline const int64_t test_abs_neg = i_abs(static_cast<int64_t>(
      (UINT64_C(0) - UINT64_C(42)) & UINT64_C(9223372036854775807)));
};
