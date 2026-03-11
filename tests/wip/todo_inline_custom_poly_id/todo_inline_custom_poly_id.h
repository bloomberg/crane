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
    unsigned int kept_nat = _anon_alias(4u);
    bool kept_bool = _anon_alias(true);
    if (kept_bool) {
      return (std::move(kept_nat) + 1);
    } else {
      return 0u;
    }
  }();
};
template <typename T1> T1 _anon_alias() {
  return [](const T1 _x0) { return inline_id_impl; };
}
