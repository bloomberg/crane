#include <z_gmp.h>

mpz_class ZGMPTest::add_test(const mpz_class &_x0, const mpz_class &_x1) {
  return (_x0 + _x1);
}

mpz_class ZGMPTest::mul_test(const mpz_class &_x0, const mpz_class &_x1) {
  return (_x0 * _x1);
}

mpz_class ZGMPTest::sub_test(const mpz_class &_x0, const mpz_class &_x1) {
  return (_x0 - _x1);
}

mpz_class ZGMPTest::abs_test(const mpz_class &_x0) { return abs(_x0); }

mpz_class ZGMPTest::opp_test(const mpz_class &_x0) { return (-_x0); }

bool ZGMPTest::eqb_test(const mpz_class &_x0, const mpz_class &_x1) {
  return _x0 == _x1;
}

bool ZGMPTest::ltb_test(const mpz_class &_x0, const mpz_class &_x1) {
  return _x0 < _x1;
}

bool ZGMPTest::leb_test(const mpz_class &_x0, const mpz_class &_x1) {
  return _x0 <= _x1;
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
