#include "todo_inline_custom_symbol.h"

uint64_t TodoInlineCustomSymbol::alias(uint64_t x0_) {
  return inline_inc_impl(x0_);
}

uint64_t TodoInlineCustomSymbol::twice(uint64_t n) { return alias(alias(n)); }
