#pragma once

#include <cstdint>
#include <todo_inline_custom_symbol_support.h>

struct TodoInlineCustomSymbol {
  static uint64_t alias(uint64_t x0_);
  static uint64_t twice(uint64_t n);
  static inline const uint64_t test_value = twice(UINT64_C(3));
};
