#ifndef INCLUDED_TODO_INLINE_CUSTOM_SYMBOL
#define INCLUDED_TODO_INLINE_CUSTOM_SYMBOL

#include <todo_inline_custom_symbol_support.h>

struct TodoInlineCustomSymbol {
  static unsigned int alias(unsigned int _x0);
  static unsigned int twice(unsigned int n);
  static inline const unsigned int test_value = twice(3u);
};

#endif // INCLUDED_TODO_INLINE_CUSTOM_SYMBOL
