#include <sections_modules.h>

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

__attribute__((pure)) unsigned int
SectionsModules::add_params(const unsigned int x, const unsigned int y,
                            const unsigned int n) {
  return ((n + x) + y);
}

__attribute__((pure)) unsigned int
SectionsModules::count_down_from_x(const unsigned int x, const unsigned int y,
                                   const unsigned int n) {
  if (n <= 0) {
    return std::move(x);
  } else {
    unsigned int n_ = n - 1;
    return (count_down_from_x(x, std::move(y), n_) + std::move(y));
  }
}

__attribute__((pure)) unsigned int
SectionsModules::NatMonoid::op(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int
SectionsModules::LocalDefs::private_helper(const unsigned int n) {
  return (n * 2u);
}

__attribute__((pure)) unsigned int
SectionsModules::LocalDefs::public_use(const unsigned int n) {
  return (private_helper(n) + 1u);
}

__attribute__((pure)) unsigned int
SectionsModules::use_both(const unsigned int a, const unsigned int b,
                          const unsigned int c) {
  return ((a + b) + c);
}

__attribute__((pure)) unsigned int
SectionsModules::use_outer(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int
SectionsModules::Base::base_fun(const unsigned int n) {
  return (n + 1u);
}

__attribute__((pure)) unsigned int
SectionsModules::Extended::base_fun(const unsigned int n) {
  return (n + 1u);
}

__attribute__((pure)) unsigned int
SectionsModules::Extended::extended_fun(const unsigned int n) {
  return (base_fun(n) + extended_val);
}
