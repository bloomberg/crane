#include <n_gmp.h>

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
#include <utility>
#include <variant>

__attribute__((pure)) mpz_class Pos::add_carry(const mpz_class x,
                                               const mpz_class y) {
  if (x == 1) {
    if (y == 1) {
      return (2 * mpz_class(1) + 1);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * (q + 1) + 1);
    } else {
      mpz_class q = y / 2;
      return (2 * (q + 1));
    }
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return (2 * (p + 1) + 1);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * add_carry(p, q) + 1);
    } else {
      mpz_class q = y / 2;
      return (2 * add_carry(p, q));
    }
  } else {
    mpz_class p = x / 2;
    if (y == 1) {
      return (2 * (p + 1));
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * add_carry(p, q));
    } else {
      mpz_class q = y / 2;
      return (2 * (p + q) + 1);
    }
  }
}

__attribute__((pure)) mpz_class NGMPTest::add_test(const mpz_class _x0,
                                                   const mpz_class _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) mpz_class NGMPTest::mul_test(const mpz_class _x0,
                                                   const mpz_class _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) mpz_class NGMPTest::sub_test(const mpz_class _x0,
                                                   const mpz_class _x1) {
  return (_x0 >= _x1 ? _x0 - _x1 : mpz_class(0));
}

__attribute__((pure)) mpz_class NGMPTest::div_test(const mpz_class _x0,
                                                   const mpz_class _x1) {
  return (_x1 == 0 ? mpz_class(0) : _x0 / _x1);
}

__attribute__((pure)) bool NGMPTest::eqb_test(const mpz_class _x0,
                                              const mpz_class _x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool NGMPTest::ltb_test(const mpz_class _x0,
                                              const mpz_class _x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool NGMPTest::leb_test(const mpz_class _x0,
                                              const mpz_class _x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) mpz_class NGMPTest::succ_test(const mpz_class _x0) {
  return (_x0 + 1);
}

__attribute__((pure)) mpz_class NGMPTest::pred_test(const mpz_class _x0) {
  return (_x0 == 0 ? mpz_class(0) : _x0 - 1);
}

__attribute__((pure)) mpz_class NGMPTest::double_test(const mpz_class _x0) {
  return (_x0 * 2);
}

__attribute__((pure)) bool NGMPTest::is_zero(const mpz_class n) {
  if (n == 0) {
    return true;
  } else {
    mpz_class _x = n;
    return false;
  }
}

__attribute__((pure)) mpz_class NGMPTest::pos_add(const mpz_class _x0,
                                                  const mpz_class _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) mpz_class NGMPTest::pos_succ(const mpz_class _x0) {
  return (_x0 + 1);
}
