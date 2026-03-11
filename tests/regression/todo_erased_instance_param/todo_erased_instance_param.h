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
concept Default = requires {
  { I::def() } -> std::convertible_to<A>;
};

struct TodoErasedInstanceParam {
  struct natDefault {
    static unsigned int def() { return 4u; }
  };
  static_assert(Default<natDefault, unsigned int>);

  template <typename _tcI0, typename T1> static T1 pick() {
    return _tcI0::def();
  }

  static inline const unsigned int test_value =
      (pick<natDefault, unsigned int>() + pick<natDefault, unsigned int>());
};
