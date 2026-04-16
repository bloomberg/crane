#ifndef INCLUDED_TODO_INLINE_CUSTOM_SYMBOL
#define INCLUDED_TODO_INLINE_CUSTOM_SYMBOL

#include <todo_inline_custom_symbol_support.h>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct TodoInlineCustomSymbol {
  __attribute__((pure)) static unsigned int alias(const unsigned int _x0);
  __attribute__((pure)) static unsigned int twice(const unsigned int n);
  static inline const unsigned int test_value = twice(3u);
};

#endif // INCLUDED_TODO_INLINE_CUSTOM_SYMBOL
