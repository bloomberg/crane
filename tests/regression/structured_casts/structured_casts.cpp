#include "structured_casts.h"

int64_t StructuredCasts::f_wrap_u8(int64_t x0_) {
  return static_cast<int64_t>(static_cast<uint8_t>(x0_));
}

int64_t StructuredCasts::f_wrap_i8(int64_t x0_) {
  return static_cast<int64_t>(static_cast<int8_t>(x0_));
}

int64_t StructuredCasts::f_sat_u8(int64_t x0_) {
  return static_cast<int64_t>(std::saturate_cast<uint8_t>(x0_));
}

int64_t StructuredCasts::f_sat_i8(int64_t x0_) {
  return static_cast<int64_t>(std::saturate_cast<int8_t>(x0_));
}

bool StructuredCasts::f_is_size_max(int64_t x0_) {
  return static_cast<std::size_t>(x0_) == 18446744073709551615uz;
}

bool StructuredCasts::f_is_u64_max(uint64_t x0_) {
  return x0_ == UINT64_C(18446744073709551615);
}

int64_t StructuredCasts::f_low_byte(uint64_t x0_) {
  return static_cast<int64_t>(static_cast<uint8_t>(x0_));
}

int64_t StructuredCasts::f_same(int64_t x0_) { return x0_; }
