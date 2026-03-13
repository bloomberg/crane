#include <modpath_escape_collision.h>

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
ModpathEscapeCollision::A::Token_::f(const unsigned int n) {
  return std::move(n);
}

__attribute__((pure)) unsigned int
ModpathEscapeCollision::B::Token_::g(const unsigned int n) {
  return (std::move(n) + 1);
}
