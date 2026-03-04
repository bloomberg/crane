#include <algorithm>
#include <any>
#include <cassert>
#include <escape_collision_class.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int EscapeCollisionClass::class_(const unsigned int n) {
  return std::move(n);
}

unsigned int EscapeCollisionClass::class_(const unsigned int n) {
  return (std::move(n) + 1);
}
