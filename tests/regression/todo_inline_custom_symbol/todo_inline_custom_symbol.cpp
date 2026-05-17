#include "todo_inline_custom_symbol.h"

unsigned int TodoInlineCustomSymbol::alias(unsigned int _x0) {
  return inline_inc_impl(_x0);
}

unsigned int TodoInlineCustomSymbol::twice(unsigned int n) {
  return alias(alias(n));
}
