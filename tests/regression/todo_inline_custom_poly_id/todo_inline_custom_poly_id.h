#ifndef INCLUDED_TODO_INLINE_CUSTOM_POLY_ID
#define INCLUDED_TODO_INLINE_CUSTOM_POLY_ID

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <todo_inline_custom_poly_id_support.h>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct TodoInlineCustomPolyId {
  static inline const unsigned int test_value = [](void) {
    unsigned int kept_nat = inline_id_impl(4u);
    bool kept_bool = inline_id_impl(true);
    if (std::move(kept_bool)) {
      return (std::move(kept_nat) + 1);
    } else {
      return 0u;
    }
  }();
};

#endif // INCLUDED_TODO_INLINE_CUSTOM_POLY_ID
