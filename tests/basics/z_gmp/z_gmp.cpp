#include "z_gmp.h"

mpz_class ZGMPTest::add_test(const mpz_class &x0_, const mpz_class &x1_) {
  return (x0_ + x1_);
}

mpz_class ZGMPTest::mul_test(const mpz_class &x0_, const mpz_class &x1_) {
  return (x0_ * x1_);
}

mpz_class ZGMPTest::sub_test(const mpz_class &x0_, const mpz_class &x1_) {
  return (x0_ - x1_);
}

mpz_class ZGMPTest::abs_test(const mpz_class &x0_) { return abs(x0_); }

mpz_class ZGMPTest::opp_test(const mpz_class &x0_) { return (-x0_); }

bool ZGMPTest::eqb_test(const mpz_class &x0_, const mpz_class &x1_) {
  return x0_ == x1_;
}

bool ZGMPTest::ltb_test(const mpz_class &x0_, const mpz_class &x1_) {
  return x0_ < x1_;
}

bool ZGMPTest::leb_test(const mpz_class &x0_, const mpz_class &x1_) {
  return x0_ <= x1_;
}

mpz_class ZGMPTest::z_sign(const mpz_class &z) {
  if (z == 0) {
    return mpz_class(0);
  } else if (z > 0) {
    mpz_class _x = z;
    return mpz_class(1);
  } else {
    mpz_class _x = -z;
    return mpz_class(-1);
  }
}
