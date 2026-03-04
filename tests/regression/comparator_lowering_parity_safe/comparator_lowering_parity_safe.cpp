#include <algorithm>
#include <any>
#include <cassert>
#include <comparator_lowering_parity_safe.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ComparatorLoweringParitySafe::A::CmpLeft::f(const unsigned int n) {
  return std::move(n);
}

unsigned int
ComparatorLoweringParitySafe::B::CmpRight::g(const unsigned int n) {
  return (std::move(n) + 1);
}
