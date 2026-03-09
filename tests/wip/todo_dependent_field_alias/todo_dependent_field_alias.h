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

template <typename I, typename carrier>
concept Magma = requires(carrier a0, carrier a1) {
  { I::op(a1, a0) } -> std::convertible_to<carrier>;
};

struct TodoDependentFieldAlias {
  using carrier = std::any;

  template <typename _tcI0, typename carrier>
  static carrier op(const carrier _x0, const carrier _x1) {
    return _tcI0::op(_x0, _x1);
  }

  struct nat_magma {
    static unsigned int op(unsigned int a0, unsigned int a1) {
      return (a0 + a1);
    }
  };
  static_assert(Magma<nat_magma, unsigned int>);

  template <typename _tcI0, typename carrier>
  static carrier pick_op(const carrier _x0, const carrier _x1) {
    return _tcI0::op(_x0, _x1);
  }

  static inline const unsigned int test_value = [](void) {
    std::function<std::any(std::any, std::any)> alias = [](const carrier _x0,
                                                           const carrier _x1) {
      return pick_op<nat_magma>(_x0, _x1);
    };
    return alias(((0 + 1) + 1), (((0 + 1) + 1) + 1));
  }();
};
