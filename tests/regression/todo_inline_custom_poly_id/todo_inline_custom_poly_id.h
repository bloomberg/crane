#ifndef INCLUDED_TODO_INLINE_CUSTOM_POLY_ID
#define INCLUDED_TODO_INLINE_CUSTOM_POLY_ID

#include <todo_inline_custom_poly_id_support.h>

struct TodoInlineCustomPolyId {
  static inline const uint64_t test_value = []() {
    uint64_t kept_nat = inline_id_impl(UINT64_C(4));
    bool kept_bool = inline_id_impl(true);
    if (kept_bool) {
      return (kept_nat + 1);
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_TODO_INLINE_CUSTOM_POLY_ID
