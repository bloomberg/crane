#ifndef INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS
#define INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS

#include <any>
#include <functional>
#include <type_traits>

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

  template <Pack _tcI0>
  __attribute__((pure)) static typename _tcI0::carrier
  step_of(const typename _tcI0::carrier _x0) {
    return _tcI0::step(_x0);
  }

  template <Pack _tcI0>
  __attribute__((pure)) static typename _tcI0::carrier run_twice() {
    std::function<typename _tcI0::carrier(typename _tcI0::carrier)> alias =
        [](typename _tcI0::carrier _x0) ->
        typename _tcI0::carrier { return step_of<_tcI0>(_x0); };
    return alias(alias(_tcI0::seed()));
  }

  struct nat_pack {
    using carrier = unsigned int;

    constexpr static unsigned int seed() { return 3u; }

    constexpr static unsigned int step(unsigned int x) { return (x + 1); }
  };

  static_assert(Pack<nat_pack>);
  static inline const unsigned int test_value = run_twice<nat_pack>();
};

#endif // INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS
