#ifndef INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS
#define INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS

#include <any>
#include <concepts>
#include <functional>
#include <utility>

template <typename
I>concept Pack = requires {
  typename I::carrier;
  { I::step(std::declval<typename I::carrier>()) } -> std::convertible_to<typename I::carrier>;
} && (requires {
  { I::seed() } -> std::convertible_to<typename I::carrier>;
} || requires {
  { I::seed } -> std::convertible_to<typename I::carrier>;
});

struct TodoTypeSubstPackAlias {
  using carrier = std::any;

  template <Pack _tcI0>
  static typename _tcI0::carrier step_of(const typename _tcI0::carrier &_x0) {
    return _tcI0::step(_x0);
  }

  template <Pack _tcI0> static typename _tcI0::carrier run_twice() {
    std::function<typename _tcI0::carrier(typename _tcI0::carrier)> alias =
        [](typename _tcI0::carrier _x0) ->
        typename _tcI0::carrier { return step_of<_tcI0>(_x0); };
    return alias(alias(_tcI0::seed()));
  }

  struct nat_pack {
    using carrier = uint64_t;

    static uint64_t seed() { return UINT64_C(3); }

    static uint64_t step(uint64_t x) { return (std::move(x) + 1); }
  };

  static_assert(Pack<nat_pack>);
  static inline const uint64_t test_value =
      std::any_cast<uint64_t>(run_twice<nat_pack>());
};

#endif // INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS
