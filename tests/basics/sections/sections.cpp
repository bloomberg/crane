#include "sections.h"

unsigned int Sections::add_n(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int Sections::mul_n(unsigned int _x0, unsigned int _x1) {
  return (_x0 * _x1);
}

unsigned int Sections::add_five(unsigned int _x0) { return add_n(5u, _x0); }

unsigned int Sections::mul_three(unsigned int _x0) { return mul_n(3u, _x0); }

unsigned int Sections::sum_ab(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int Sections::prod_ab(unsigned int _x0, unsigned int _x1) {
  return (_x0 * _x1);
}

unsigned int Sections::use_inner(unsigned int a) { return sum_ab(a, 3u); }
