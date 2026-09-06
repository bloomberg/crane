#include "sections.h"

uint64_t Sections::add_n(uint64_t x0_, uint64_t x1_) { return (x0_ + x1_); }

uint64_t Sections::mul_n(uint64_t x0_, uint64_t x1_) { return (x0_ * x1_); }

uint64_t Sections::add_five(uint64_t x0_) { return add_n(UINT64_C(5), x0_); }

uint64_t Sections::mul_three(uint64_t x0_) { return mul_n(UINT64_C(3), x0_); }

uint64_t Sections::sum_ab(uint64_t x0_, uint64_t x1_) { return (x0_ + x1_); }

uint64_t Sections::prod_ab(uint64_t x0_, uint64_t x1_) { return (x0_ * x1_); }

uint64_t Sections::use_inner(uint64_t a) { return sum_ab(a, UINT64_C(3)); }
