#include "bool_ops.h"

bool BoolOps::my_negb(bool b) {
  if (b) {
    return false;
  } else {
    return true;
  }
}

bool BoolOps::my_andb(bool a, bool b) {
  if (a) {
    return b;
  } else {
    return false;
  }
}

bool BoolOps::my_orb(bool a, bool b) {
  if (a) {
    return true;
  } else {
    return b;
  }
}

bool BoolOps::my_xorb(bool a, bool b) {
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

unsigned int BoolOps::if_nat(bool b, unsigned int t, unsigned int f) {
  if (b) {
    return t;
  } else {
    return f;
  }
}

bool BoolOps::complex_bool(bool a, bool b, bool c) {
  return my_orb(my_andb(a, b), my_andb(my_negb(a), c));
}

bool BoolOps::nat_eq(unsigned int _x0, unsigned int _x1) { return _x0 == _x1; }

bool BoolOps::nat_lt(unsigned int _x0, unsigned int _x1) { return _x0 < _x1; }

bool BoolOps::nat_le(unsigned int _x0, unsigned int _x1) { return _x0 <= _x1; }
