#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nth_default_struct_safe.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int NthDefaultStructSafe::L::SlotLeft::nth0(const unsigned int n) {
  return std::move(n);
}

unsigned int NthDefaultStructSafe::R::SlotRight::nth1(const unsigned int n) {
  return (std::move(n) + 1);
}
