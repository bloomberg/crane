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

template <typename I, typename A>
concept Boxed = requires {
  { I::boxed_default() } -> std::convertible_to<A>;
};

struct TodoTypeAppInstanceAlias {
  struct natBoxed {
    static unsigned int boxed_default() { return 7u; }
  };
  static_assert(Boxed<natBoxed, unsigned int>);

  template <typename _tcI0, typename T1> static T1 pick() {
    return _tcI0::boxed_default();
  }

  static inline const unsigned int test_value = [](void) {
    return (_anon_alias(natBoxed) + _anon_alias(natBoxed));
  }();
};
template <typename T1> T1 _anon_alias() {
  return TodoTypeAppInstanceAlias::pick;
}
