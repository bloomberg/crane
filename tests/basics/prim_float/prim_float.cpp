#include <prim_float.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) double PrimFloat::test_add(const double _x0,
                                                 const double _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) double PrimFloat::test_sub(const double _x0,
                                                 const double _x1) {
  return (_x0 - _x1);
}

__attribute__((pure)) double PrimFloat::test_mul(const double _x0,
                                                 const double _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) double PrimFloat::test_div(const double _x0,
                                                 const double _x1) {
  return (_x0 / _x1);
}

__attribute__((pure)) double PrimFloat::test_opp(const double _x0) {
  return (-_x0);
}

__attribute__((pure)) double PrimFloat::test_abs(const double _x0) {
  return std::abs(_x0);
}

__attribute__((pure)) double PrimFloat::test_sqrt(const double _x0) {
  return std::sqrt(_x0);
}

__attribute__((pure)) bool PrimFloat::test_eqb(const double _x0,
                                               const double _x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool PrimFloat::test_ltb(const double _x0,
                                               const double _x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool PrimFloat::test_leb(const double _x0,
                                               const double _x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) double PrimFloat::test_of_uint63(const int64_t _x0) {
  return static_cast<double>(_x0);
}
