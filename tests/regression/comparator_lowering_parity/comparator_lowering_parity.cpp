#include <algorithm>
#include <any>
#include <cassert>
#include <comparator_lowering_parity.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ComparatorLoweringParity::A::Value_::f(const unsigned int n) {
  return std::move(n);
}

unsigned int ComparatorLoweringParity::B::Value_::g(const unsigned int n) {
  return (std::move(n) + 1);
}
