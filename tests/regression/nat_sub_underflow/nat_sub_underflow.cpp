#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nat_sub_underflow.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int NatSubUnderflow::value_(const unsigned int n) {
  return std::move(n);
}

unsigned int NatSubUnderflow::value_0(const unsigned int n) {
  return (std::move(n) + 1);
}
