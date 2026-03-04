#include <algorithm>
#include <any>
#include <cassert>
#include <escape_collision.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int EscapeCollision::double_(const unsigned int n) {
  return std::move(n);
}

unsigned int EscapeCollision::double_0(const unsigned int n) {
  return (std::move(n) + 1);
}
