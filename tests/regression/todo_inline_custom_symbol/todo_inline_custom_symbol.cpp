#include "todo_inline_custom_symbol.h"

uint64_t TodoInlineCustomSymbol::alias(uint64_t _x0) {
  return inline_inc_impl(_x0);
}

uint64_t TodoInlineCustomSymbol::twice(uint64_t n) { return alias(alias(n)); }
