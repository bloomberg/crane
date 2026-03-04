#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nth_default_struct.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int NthDefaultStruct::A::Value_::f(const unsigned int n) {
  return std::move(n);
}

unsigned int NthDefaultStruct::B::Value_::g(const unsigned int n) {
  return (std::move(n) + 1);
}
