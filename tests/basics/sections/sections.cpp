#include <sections.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int Sections::add_n(const unsigned int _x0,
                                                   const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int Sections::mul_n(const unsigned int _x0,
                                                   const unsigned int _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) unsigned int Sections::add_five(const unsigned int _x0) {
  return add_n(5u, _x0);
}

__attribute__((pure)) unsigned int Sections::mul_three(const unsigned int _x0) {
  return mul_n(3u, _x0);
}

__attribute__((pure)) unsigned int Sections::sum_ab(const unsigned int _x0,
                                                    const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int Sections::prod_ab(const unsigned int _x0,
                                                     const unsigned int _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) unsigned int Sections::use_inner(const unsigned int a) {
  return sum_ab(a, 3u);
}
