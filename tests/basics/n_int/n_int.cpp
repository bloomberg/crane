#include <n_int.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int Pos::add_carry(const unsigned int &x,
                                                  const unsigned int &y) {
  if (x == 1u) {
    if (y == 1u) {
      return (2u * 1u + 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * (q + 1u) + 1u);
    } else {
      unsigned int q = y / 2u;
      return (2u * (q + 1u));
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return (2u * (p + 1u) + 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add_carry(p, q) + 1u);
    } else {
      unsigned int q = y / 2u;
      return (2u * add_carry(p, q));
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return (2u * (p + 1u));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return (2u * (p + q) + 1u);
    }
  }
}

__attribute__((pure)) unsigned int NIntTest::add_test(const unsigned int &_x0,
                                                      const unsigned int &_x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int NIntTest::mul_test(const unsigned int &_x0,
                                                      const unsigned int &_x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) unsigned int NIntTest::sub_test(const unsigned int &_x0,
                                                      const unsigned int &_x1) {
  return (_x0 >= _x1 ? _x0 - _x1 : 0u);
}

__attribute__((pure)) unsigned int NIntTest::div_test(const unsigned int &_x0,
                                                      const unsigned int &_x1) {
  return (_x1 == 0u ? 0u : _x0 / _x1);
}

__attribute__((pure)) bool NIntTest::eqb_test(const unsigned int &_x0,
                                              const unsigned int &_x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool NIntTest::ltb_test(const unsigned int &_x0,
                                              const unsigned int &_x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool NIntTest::leb_test(const unsigned int &_x0,
                                              const unsigned int &_x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) unsigned int
NIntTest::succ_test(const unsigned int &_x0) {
  return (_x0 + 1u);
}

__attribute__((pure)) unsigned int
NIntTest::pred_test(const unsigned int &_x0) {
  return (_x0 == 0u ? 0u : _x0 - 1u);
}

__attribute__((pure)) unsigned int
NIntTest::double_test(const unsigned int &_x0) {
  return (_x0 * 2u);
}

__attribute__((pure)) bool NIntTest::is_zero(const unsigned int &n) {
  if (n == 0u) {
    return true;
  } else {
    unsigned int _x = n;
    return false;
  }
}

__attribute__((pure)) unsigned int NIntTest::pos_add(const unsigned int &_x0,
                                                     const unsigned int &_x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int NIntTest::pos_succ(const unsigned int &_x0) {
  return (_x0 + 1u);
}
