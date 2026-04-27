#include <todo_inline_custom_symbol.h>

__attribute__((pure)) unsigned int
TodoInlineCustomSymbol::alias(const unsigned int &_x0) {
  return inline_inc_impl(_x0);
}

__attribute__((pure)) unsigned int
TodoInlineCustomSymbol::twice(const unsigned int &n) {
  return alias(alias(n));
}
