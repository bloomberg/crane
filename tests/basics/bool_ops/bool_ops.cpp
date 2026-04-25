#include <bool_ops.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) bool BoolOps::my_negb(const bool &b) {
  if (b) {
    return false;
  } else {
    return true;
  }
}

__attribute__((pure)) bool BoolOps::my_andb(const bool &a, bool b) {
  if (a) {
    return b;
  } else {
    return false;
  }
}

__attribute__((pure)) bool BoolOps::my_orb(const bool &a, bool b) {
  if (a) {
    return true;
  } else {
    return b;
  }
}

__attribute__((pure)) bool BoolOps::my_xorb(const bool &a, const bool &b) {
  if (a) {
    if (b) {
      return false;
    } else {
      return true;
    }
  } else {
    if (b) {
      return true;
    } else {
      return false;
    }
  }
}

__attribute__((pure)) unsigned int
BoolOps::if_nat(const bool &b, unsigned int t, unsigned int f) {
  if (b) {
    return t;
  } else {
    return f;
  }
}

__attribute__((pure)) bool BoolOps::complex_bool(const bool &a, const bool &b,
                                                 const bool &c) {
  return my_orb(my_andb(a, b), my_andb(my_negb(a), c));
}

__attribute__((pure)) bool BoolOps::nat_eq(const unsigned int &_x0,
                                           const unsigned int &_x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool BoolOps::nat_lt(const unsigned int &_x0,
                                           const unsigned int &_x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool BoolOps::nat_le(const unsigned int &_x0,
                                           const unsigned int &_x1) {
  return _x0 <= _x1;
}
