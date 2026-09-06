#include "z_int.h"

int64_t ZIntTest::add_test(int64_t x0_, int64_t x1_) {
  return static_cast<int64_t>(static_cast<uint64_t>(x0_) +
                              static_cast<uint64_t>(x1_));
}

int64_t ZIntTest::mul_test(int64_t x0_, int64_t x1_) {
  return static_cast<int64_t>(static_cast<uint64_t>(x0_) *
                              static_cast<uint64_t>(x1_));
}

int64_t ZIntTest::sub_test(int64_t x0_, int64_t x1_) {
  return static_cast<int64_t>(static_cast<uint64_t>(x0_) -
                              static_cast<uint64_t>(x1_));
}

int64_t ZIntTest::abs_test(int64_t x0_) {
  return (x0_ < 0 ? static_cast<int64_t>(-static_cast<uint64_t>(x0_)) : x0_);
}

int64_t ZIntTest::opp_test(int64_t x0_) {
  return static_cast<int64_t>(-static_cast<uint64_t>(x0_));
}

bool ZIntTest::eqb_test(int64_t x0_, int64_t x1_) { return x0_ == x1_; }

bool ZIntTest::ltb_test(int64_t x0_, int64_t x1_) { return x0_ < x1_; }

bool ZIntTest::leb_test(int64_t x0_, int64_t x1_) { return x0_ <= x1_; }

int64_t ZIntTest::z_sign(int64_t z) {
  if (z == 0) {
    return INT64_C(0);
  } else if (z > 0) {
    unsigned int _x = static_cast<unsigned int>(z);
    return INT64_C(1);
  } else {
    unsigned int _x = static_cast<unsigned int>(-z);
    return INT64_C(-1);
  }
}
