#ifndef INCLUDED_TODO_EXTRACT_CONSTANT_NONINLINE
#define INCLUDED_TODO_EXTRACT_CONSTANT_NONINLINE

#include <todo_extract_constant_noninline_support.h>

struct TodoExtractConstantNoninline {
  static uint64_t foreign_inc(uint64_t _x0);
  static inline const uint64_t test_value = foreign_inc(UINT64_C(4));
  static inline const uint64_t twice_value =
      foreign_inc(foreign_inc(UINT64_C(2)));
};

#endif // INCLUDED_TODO_EXTRACT_CONSTANT_NONINLINE
