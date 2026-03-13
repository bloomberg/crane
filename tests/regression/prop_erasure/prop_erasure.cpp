#include <prop_erasure.h>

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
PropErasure::with_proof_arg(const unsigned int n) {
  return std::move(n);
}

__attribute__((pure)) unsigned int
PropErasure::add_with_proof(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}
