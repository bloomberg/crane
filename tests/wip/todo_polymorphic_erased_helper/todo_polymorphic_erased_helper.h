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

struct TodoPolymorphicErasedHelper {
  static inline const unsigned int test_value = []() {
    return [](void) {
      unsigned int kept_nat =
          _anon_aux((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));
      bool kept_bool = _anon_aux(true);
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
template <typename T1> T1 _anon_aux(const T1 x) { return x; }
