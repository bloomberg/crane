#ifndef INCLUDED_TODO_EXTRACT_CONSTANT_NONINLINE
#define INCLUDED_TODO_EXTRACT_CONSTANT_NONINLINE

#include <memory>
#include <optional>
#include <todo_extract_constant_noninline_support.h>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct TodoExtractConstantNoninline {
  static unsigned int foreign_inc(const unsigned int &_x0);
  static inline const unsigned int test_value = foreign_inc(4u);
  static inline const unsigned int twice_value = foreign_inc(foreign_inc(2u));
};

#endif // INCLUDED_TODO_EXTRACT_CONSTANT_NONINLINE
