#include "sections_modules.h"

unsigned int SectionsModules::add_params(unsigned int x, unsigned int y,
                                         unsigned int n) {
  return ((n + x) + y);
}

unsigned int SectionsModules::count_down_from_x(unsigned int x, unsigned int y,
                                                unsigned int n) {
  if (n <= 0) {
    return x;
  } else {
    unsigned int n_ = n - 1;
    return (count_down_from_x(x, y, n_) + y);
  }
}

unsigned int SectionsModules::NatMonoid::op(unsigned int _x0,
                                            unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int SectionsModules::LocalDefs::private_helper(unsigned int n) {
  return (n * 2u);
}

unsigned int SectionsModules::LocalDefs::public_use(unsigned int n) {
  return (private_helper(n) + 1u);
}

unsigned int SectionsModules::use_both(unsigned int a, unsigned int b,
                                       unsigned int c) {
  return ((a + b) + c);
}

unsigned int SectionsModules::use_outer(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int SectionsModules::Base::base_fun(unsigned int n) {
  return (n + 1u);
}

unsigned int SectionsModules::Extended::base_fun(unsigned int n) {
  return (n + 1u);
}

unsigned int SectionsModules::Extended::extended_fun(unsigned int n) {
  return (base_fun(n) + extended_val);
}
