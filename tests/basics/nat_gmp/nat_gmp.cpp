#include "nat_gmp.h"

mpz_class NatGMPTest::add_test(const mpz_class &x0_, const mpz_class &x1_) {
  return (x0_ + x1_);
}

mpz_class NatGMPTest::mul_test(const mpz_class &x0_, const mpz_class &x1_) {
  return (x0_ * x1_);
}

mpz_class NatGMPTest::sub_test(const mpz_class &x0_, const mpz_class &x1_) {
  return (x0_ >= x1_ ? x0_ - x1_ : mpz_class(0));
}

bool NatGMPTest::eqb_test(const mpz_class &x0_, const mpz_class &x1_) {
  return x0_ == x1_;
}

bool NatGMPTest::ltb_test(const mpz_class &x0_, const mpz_class &x1_) {
  return x0_ < x1_;
}

bool NatGMPTest::leb_test(const mpz_class &x0_, const mpz_class &x1_) {
  return x0_ <= x1_;
}

mpz_class NatGMPTest::pred_test(const mpz_class &x0_) {
  return (x0_ > 0 ? x0_ - 1 : x0_);
}

mpz_class NatGMPTest::match_test(const mpz_class &n) {
  if (n <= 0) {
    return mpz_class(42);
  } else {
    mpz_class m = n - 1;
    return m;
  }
}

mpz_class NatGMPTest::add_big(const mpz_class &n) {
  return (n + mpz_class(200));
}
