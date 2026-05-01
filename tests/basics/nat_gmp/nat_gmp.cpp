#include <nat_gmp.h>

mpz_class NatGMPTest::add_test(const mpz_class &_x0, const mpz_class &_x1) {
  return (_x0 + _x1);
}

mpz_class NatGMPTest::mul_test(const mpz_class &_x0, const mpz_class &_x1) {
  return (_x0 * _x1);
}

mpz_class NatGMPTest::sub_test(const mpz_class &_x0, const mpz_class &_x1) {
  return (_x0 >= _x1 ? _x0 - _x1 : mpz_class(0));
}

bool NatGMPTest::eqb_test(const mpz_class &_x0, const mpz_class &_x1) {
  return _x0 == _x1;
}

bool NatGMPTest::ltb_test(const mpz_class &_x0, const mpz_class &_x1) {
  return _x0 < _x1;
}

bool NatGMPTest::leb_test(const mpz_class &_x0, const mpz_class &_x1) {
  return _x0 <= _x1;
}

mpz_class NatGMPTest::pred_test(const mpz_class &_x0) {
  return (_x0 > 0 ? _x0 - 1 : _x0);
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
