#include <algorithm>
#include <any>
#include <bool_ops.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

bool BoolOps::my_negb(const bool b) {
  if (b) {
    return false;
  } else {
    return true;
  }
}

bool BoolOps::my_andb(const bool a, const bool b) {
  if (a) {
    return std::move(b);
  } else {
    return false;
  }
}

bool BoolOps::my_orb(const bool a, const bool b) {
  if (a) {
    return true;
  } else {
    return std::move(b);
  }
}

bool BoolOps::my_xorb(const bool a, const bool b) {
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

unsigned int BoolOps::if_nat(const bool b, const unsigned int t,
                             const unsigned int f) {
  if (b) {
    return std::move(t);
  } else {
    return std::move(f);
  }
}

bool BoolOps::complex_bool(const bool a, const bool b, const bool c) {
  return my_orb(my_andb(a, b), my_andb(my_negb(a), c));
}

bool BoolOps::nat_eq(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 == _x1);
}

bool BoolOps::nat_lt(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 < _x1);
}

bool BoolOps::nat_le(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 <= _x1);
}
