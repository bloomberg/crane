#ifndef INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS
#define INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS

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

template <typename I, typename t_A>
concept Boxed = requires {
  { I::boxed_default() } -> std::convertible_to<t_A>;
};

struct TodoTypeAppInstanceAlias {
  struct natBoxed {
    __attribute__((pure)) static unsigned int boxed_default() { return 7u; }
  };

  static_assert(Boxed<natBoxed, unsigned int>);

  template <typename _tcI0, typename T1> static T1 pick() {
    return _tcI0::boxed_default();
  }

  static inline const unsigned int test_value = [](void) {
    return (pick<natBoxed, unsigned int>() + pick<natBoxed, unsigned int>());
  }();
};

#endif // INCLUDED_TODO_TYPE_APP_INSTANCE_ALIAS
