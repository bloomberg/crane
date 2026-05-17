#include "sections.h"

uint64_t Sections::add_n(uint64_t _x0, uint64_t _x1) { return (_x0 + _x1); }

uint64_t Sections::mul_n(uint64_t _x0, uint64_t _x1) { return (_x0 * _x1); }

uint64_t Sections::add_five(uint64_t _x0) { return add_n(UINT64_C(5), _x0); }

uint64_t Sections::mul_three(uint64_t _x0) { return mul_n(UINT64_C(3), _x0); }

uint64_t Sections::sum_ab(uint64_t _x0, uint64_t _x1) { return (_x0 + _x1); }

uint64_t Sections::prod_ab(uint64_t _x0, uint64_t _x1) { return (_x0 * _x1); }

uint64_t Sections::use_inner(uint64_t a) { return sum_ab(a, UINT64_C(3)); }
