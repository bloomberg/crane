#include <escape_collision.h>

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
EscapeCollision::double_(const unsigned int n) {
  return std::move(n);
}

__attribute__((pure)) unsigned int
EscapeCollision::double_0(const unsigned int n) {
  return (std::move(n) + 1);
}
