#include "sections_modules.h"

uint64_t SectionsModules::add_params(uint64_t x, uint64_t y, uint64_t n) {
  return ((n + x) + y);
}

uint64_t SectionsModules::count_down_from_x(uint64_t x, uint64_t y,
                                            uint64_t n) {
  if (n <= 0) {
    return x;
  } else {
    uint64_t n_ = n - 1;
    return (count_down_from_x(x, y, n_) + y);
  }
}

uint64_t SectionsModules::NatMonoid::op(uint64_t _x0, uint64_t _x1) {
  return (_x0 + _x1);
}

uint64_t SectionsModules::LocalDefs::private_helper(uint64_t n) {
  return (n * UINT64_C(2));
}

uint64_t SectionsModules::LocalDefs::public_use(uint64_t n) {
  return (private_helper(n) + UINT64_C(1));
}

uint64_t SectionsModules::use_both(uint64_t a, uint64_t b, uint64_t c) {
  return ((a + b) + c);
}

uint64_t SectionsModules::use_outer(uint64_t _x0, uint64_t _x1) {
  return (_x0 + _x1);
}

uint64_t SectionsModules::Base::base_fun(uint64_t n) {
  return (n + UINT64_C(1));
}

uint64_t SectionsModules::Extended::base_fun(uint64_t n) {
  return (n + UINT64_C(1));
}

uint64_t SectionsModules::Extended::extended_fun(uint64_t n) {
  return (base_fun(n) + extended_val);
}
