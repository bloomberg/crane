#ifndef INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS
#define INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS

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
concept Pack = requires(typename I::carrier a0) {
  typename I::carrier;
  { I::step(a0) } -> std::convertible_to<typename I::carrier>;
} && requires {
  { I::seed() } -> std::convertible_to<typename I::carrier>;
} || requires {
  { I::seed } -> std::convertible_to<typename I::carrier>;
};

struct TodoTypeSubstPackAlias {
  using carrier = std::any;

  template <typename _tcI0, typename carrier>
  static carrier step_of(const carrier _x0) {
    return _tcI0::step(_x0);
  }

  template <typename _tcI0, typename carrier> static carrier run_twice() {
    std::function<carrier(carrier)> alias = [](carrier _x0) -> carrier {
      return step_of<_tcI0>(_x0);
    };
    return alias(alias(_tcI0::seed()));
  }

  struct nat_pack {
    using carrier = unsigned int;

    __attribute__((pure)) static unsigned int seed() { return 3u; }

    __attribute__((pure)) static unsigned int step(unsigned int x) {
      return (x + 1);
    }
  };

  static_assert(Pack<nat_pack>);
  static inline const unsigned int test_value =
      run_twice<nat_pack, unsigned int>();
};

#endif // INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS
