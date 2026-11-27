#pragma once

#include <cstddef>
#include <cstdint>
#include <numeric>

struct StructuredCasts {
  static int64_t f_wrap_u8(int64_t x0_);
  static int64_t f_wrap_i8(int64_t x0_);
  static int64_t f_sat_u8(int64_t x0_);
  static int64_t f_sat_i8(int64_t x0_);
  static bool f_is_size_max(int64_t x0_);
  static bool f_is_u64_max(uint64_t x0_);
  static int64_t f_low_byte(uint64_t x0_);
  static int64_t f_same(int64_t x0_);
  static inline const int64_t wrap_u8_m1 = INT64_C(255);
  static inline const int64_t wrap_u8_255 = INT64_C(255);
  static inline const int64_t wrap_u8_256 = INT64_C(0);
  static inline const int64_t wrap_i8_m1 = INT64_C(-1);
  static inline const int64_t wrap_i8_128 = INT64_C(-128);
  static inline const int64_t wrap_i8_255 = INT64_C(-1);
  static inline const int64_t sat_u8_m1 = INT64_C(0);
  static inline const int64_t sat_u8_256 = INT64_C(255);
  static inline const int64_t sat_i8_m129 = INT64_C(-128);
  static inline const int64_t sat_i8_128 = INT64_C(127);
  static inline const bool size_max_constant =
      18446744073709551615uz == 18446744073709551615uz;
  static inline const int64_t low_byte_constant = INT64_C(1);
  static inline const bool min_constant = INT64_MIN == INT64_MIN;
};
