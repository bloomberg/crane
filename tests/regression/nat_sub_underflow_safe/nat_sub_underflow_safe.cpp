#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nat_sub_underflow_safe.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int NatSubUnderflowSafe::sub_checked(const unsigned int _x0,
                                              const unsigned int _x1) {
  return (((_x0 - _x1) > _x0 ? 0 : (_x0 - _x1)));
}

unsigned int NatSubUnderflowSafe::sub_alt(const unsigned int a,
                                          const unsigned int b) {
  return (((b - a) > b ? 0 : (b - a)));
}
