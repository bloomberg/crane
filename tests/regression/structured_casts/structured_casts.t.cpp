#include <structured_casts.h>

#include <cstdint>
#include <iostream>
#include <limits>

#define M StructuredCasts

int main() {
  int fails = 0;
  auto check = [&](bool ok, const char *what) {
    if (!ok) {
      std::cout << "FAIL: " << what << std::endl;
      ++fails;
    }
  };

  check(M::f_wrap_u8(-1) == 255, "wrap_u8(-1)");
  check(M::f_wrap_u8(255) == 255, "wrap_u8(255)");
  check(M::f_wrap_u8(256) == 0, "wrap_u8(256)");
  check(M::f_wrap_i8(255) == -1, "wrap_i8(255)");
  check(M::f_wrap_i8(128) == -128, "wrap_i8(128)");
  check(M::f_sat_u8(-1) == 0, "sat_u8(-1)");
  check(M::f_sat_u8(256) == 255, "sat_u8(256)");
  check(M::f_sat_i8(-129) == -128, "sat_i8(-129)");
  check(M::f_sat_i8(128) == 127, "sat_i8(128)");
  check(M::f_is_size_max(-1), "is_size_max(-1)");
  check(!M::f_is_size_max(0), "!is_size_max(0)");
  check(M::f_is_u64_max(std::numeric_limits<uint64_t>::max()), "is_u64_max(2^64-1)");
  check(!M::f_is_u64_max(0), "!is_u64_max(0)");
  check(M::f_low_byte(257) == 1, "low_byte(257)");
  check(M::f_same(std::numeric_limits<int64_t>::min()) == std::numeric_limits<int64_t>::min(), "same(min)");

  check(M::wrap_u8_m1 == 255, "wrap_u8 -1 constant");
  check(M::wrap_u8_255 == 255, "wrap_u8 255 constant");
  check(M::wrap_u8_256 == 0, "wrap_u8 256 constant");
  check(M::wrap_i8_m1 == -1, "wrap_i8 -1 constant");
  check(M::wrap_i8_128 == -128, "wrap_i8 128 constant");
  check(M::wrap_i8_255 == -1, "wrap_i8 255 constant");
  check(M::sat_u8_m1 == 0, "sat_u8 -1 constant");
  check(M::sat_u8_256 == 255, "sat_u8 256 constant");
  check(M::sat_i8_m129 == -128, "sat_i8 -129 constant");
  check(M::sat_i8_128 == 127, "sat_i8 128 constant");
  check(M::size_max_constant, "size_max constant");
  check(M::low_byte_constant == 1, "low_byte constant");
  check(M::min_constant, "min constant");

  if (fails == 0) std::cout << "All structured_casts tests passed!" << std::endl;
  return fails;
}
