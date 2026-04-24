#include <z_int.h>

#include <cstdint>
#include <cstdlib>
#include <type_traits>

__attribute__((pure)) int64_t ZIntTest::add_test(const int64_t &_x0,
                                                 const int64_t &_x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) int64_t ZIntTest::mul_test(const int64_t &_x0,
                                                 const int64_t &_x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) int64_t ZIntTest::sub_test(const int64_t &_x0,
                                                 const int64_t &_x1) {
  return (_x0 - _x1);
}

__attribute__((pure)) int64_t ZIntTest::abs_test(const int64_t &_x0) {
  return std::abs(_x0);
}

__attribute__((pure)) int64_t ZIntTest::opp_test(const int64_t &_x0) {
  return (-_x0);
}

__attribute__((pure)) bool ZIntTest::eqb_test(const int64_t &_x0,
                                              const int64_t &_x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool ZIntTest::ltb_test(const int64_t &_x0,
                                              const int64_t &_x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool ZIntTest::leb_test(const int64_t &_x0,
                                              const int64_t &_x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) int64_t ZIntTest::z_sign(const int64_t &z) {
  if (z == 0) {
    return INT64_C(0);
  } else if (z > 0) {
    unsigned int _x = static_cast<unsigned int>(z);
    return INT64_C(1);
  } else {
    unsigned int _x = static_cast<unsigned int>(-z);
    return INT64_C(-1);
  }
}
