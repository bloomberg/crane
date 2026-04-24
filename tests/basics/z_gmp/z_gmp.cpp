#include <z_gmp.h>

#include <gmpxx.h>
#include <type_traits>

__attribute__((pure)) mpz_class ZGMPTest::add_test(const mpz_class &_x0,
                                                   const mpz_class &_x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) mpz_class ZGMPTest::mul_test(const mpz_class &_x0,
                                                   const mpz_class &_x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) mpz_class ZGMPTest::sub_test(const mpz_class &_x0,
                                                   const mpz_class &_x1) {
  return (_x0 - _x1);
}

__attribute__((pure)) mpz_class ZGMPTest::abs_test(const mpz_class &_x0) {
  return abs(_x0);
}

__attribute__((pure)) mpz_class ZGMPTest::opp_test(const mpz_class &_x0) {
  return (-_x0);
}

__attribute__((pure)) bool ZGMPTest::eqb_test(const mpz_class &_x0,
                                              const mpz_class &_x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool ZGMPTest::ltb_test(const mpz_class &_x0,
                                              const mpz_class &_x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool ZGMPTest::leb_test(const mpz_class &_x0,
                                              const mpz_class &_x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) mpz_class ZGMPTest::z_sign(const mpz_class &z) {
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
