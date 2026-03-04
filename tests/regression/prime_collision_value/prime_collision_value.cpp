#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prime_collision_value.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int PrimeCollisionValue::value_(const unsigned int n) {
  return std::move(n);
}

unsigned int PrimeCollisionValue::value_0(const unsigned int n) {
  return (std::move(n) + 1);
}
