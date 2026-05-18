#include "prim_float.h"

double PrimFloat::test_add(double _x0, double _x1) { return (_x0 + _x1); }

double PrimFloat::test_sub(double _x0, double _x1) { return (_x0 - _x1); }

double PrimFloat::test_mul(double _x0, double _x1) { return (_x0 * _x1); }

double PrimFloat::test_div(double _x0, double _x1) { return (_x0 / _x1); }

double PrimFloat::test_opp(double _x0) { return (-_x0); }

double PrimFloat::test_abs(double _x0) { return std::abs(_x0); }

double PrimFloat::test_sqrt(double _x0) { return std::sqrt(_x0); }

bool PrimFloat::test_eqb(double _x0, double _x1) { return _x0 == _x1; }

bool PrimFloat::test_ltb(double _x0, double _x1) { return _x0 < _x1; }

bool PrimFloat::test_leb(double _x0, double _x1) { return _x0 <= _x1; }

double PrimFloat::test_of_uint63(int64_t _x0) {
  return static_cast<double>(_x0);
}
