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

struct TodoLetinAppliedPoly {
  static inline const unsigned int demo_nat =
      (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1);

  static inline const bool demo_bool = true;

  static inline const unsigned int test_value = [](void) {
    if (demo_bool) {
      return demo_nat;
    } else {
      return 0;
    }
  }();
};
