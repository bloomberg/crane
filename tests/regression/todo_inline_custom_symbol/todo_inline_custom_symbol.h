#ifndef INCLUDED_TODO_INLINE_CUSTOM_SYMBOL
#define INCLUDED_TODO_INLINE_CUSTOM_SYMBOL

#include <todo_inline_custom_symbol_support.h>

struct TodoInlineCustomSymbol {
  static uint64_t alias(uint64_t _x0);
  static uint64_t twice(uint64_t n);
  static inline const uint64_t test_value = twice(UINT64_C(3));
};

#endif // INCLUDED_TODO_INLINE_CUSTOM_SYMBOL
