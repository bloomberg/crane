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

template <typename I>
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a1, a0) } -> std::convertible_to<typename I::carrier>;
};

struct TodoDependentFieldAlias {
  using carrier = std::any;

  struct nat_magma {
    using carrier = unsigned int;
    static unsigned int op(unsigned int a0, unsigned int a1) {
      return (a0 + a1);
    }
  };
  static_assert(Magma<nat_magma>);

  template <typename _tcI0, typename carrier>
  static carrier pick_op(const carrier _x0, const carrier _x1) {
    return _tcI0::op(_x0, _x1);
  }

  static inline const unsigned int test_value = [](void) {
    std::function<unsigned int(unsigned int, unsigned int)> alias =
        [](const unsigned int _x0, const unsigned int _x1) -> unsigned int {
      return pick_op<nat_magma>(_x0, _x1);
    };
    return alias(2u, 3u);
  }();
};
