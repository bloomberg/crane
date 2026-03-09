#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct TodoExplicitTypeAppAlias {
  template <typename T1> static T1 id(const T1 x) { return x; }

  static inline const unsigned int test_value = []() {
    return [](void) {
      unsigned int kept_nat =
          _anon_alias((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
      bool kept_bool = _anon_alias(true);
      return (std::move(kept_nat) + [&](void) {
        if (std::move(kept_bool)) {
          return (0 + 1);
        } else {
          return 0;
        }
      }());
    }();
  }();
};
template <typename T1> T1 _anon_alias() { return TodoExplicitTypeAppAlias::id; }
