#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prime_collision.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int PrimeCollision::foo_(const unsigned int n) { return std::move(n); }

unsigned int PrimeCollision::foo_0(const unsigned int n) {
  return (std::move(n) + 1);
}
