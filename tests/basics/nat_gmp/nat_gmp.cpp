#include <nat_gmp.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <gmpxx.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) mpz_class NatGMPTest::add_test(const mpz_class _x0,
                                                     const mpz_class _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) mpz_class NatGMPTest::mul_test(const mpz_class _x0,
                                                     const mpz_class _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) mpz_class NatGMPTest::sub_test(const mpz_class _x0,
                                                     const mpz_class _x1) {
  return (_x0 >= _x1 ? _x0 - _x1 : mpz_class(0));
}

__attribute__((pure)) bool NatGMPTest::eqb_test(const mpz_class _x0,
                                                const mpz_class _x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool NatGMPTest::ltb_test(const mpz_class _x0,
                                                const mpz_class _x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool NatGMPTest::leb_test(const mpz_class _x0,
                                                const mpz_class _x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) mpz_class NatGMPTest::pred_test(const mpz_class _x0) {
  return (_x0 > 0 ? _x0 - 1 : _x0);
}

__attribute__((pure)) mpz_class NatGMPTest::match_test(const mpz_class n) {
  if (n <= 0) {
    return mpz_class(42);
  } else {
    mpz_class m = n - 1;
    return m;
  }
}

__attribute__((pure)) mpz_class NatGMPTest::add_big(const mpz_class n) {
  return (n + mpz_class(200));
}
