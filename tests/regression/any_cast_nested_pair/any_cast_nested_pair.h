#pragma once

#include "obj.h"
#include <cstdint>
#include <utility>
#include <variant>

struct AnyCastNestedPair {
  using SemVal = crane::obj /* AXIOM TO BE REALIZED */;
  using symbols_semty = crane::obj;
  static uint64_t apply_pred(symbols_semty input);
  static uint64_t test_pred(uint64_t a, uint64_t b);
};
