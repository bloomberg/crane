#ifndef INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS
#define INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS

#include <any>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

template <typename I>
concept Pack = requires (typename I::carrier
a0) {
  typename I::carrier;
  { I::step(a0) } -> std::convertible_to<typename I::carrier>;
} && (requires {
  { I::seed() } -> std::convertible_to<typename I::carrier>;
} || requires {
  { I::seed } -> std::convertible_to<typename I::carrier>;
});

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

    __attribute__((pure)) static unsigned int seed() { return 3u; }

    __attribute__((pure)) static unsigned int step(unsigned int x) {
      return (x + 1);
    }
  };

  static_assert(Pack<nat_pack>);
  static inline const unsigned int test_value =
      std::any_cast<unsigned int>(run_twice<nat_pack>());
};

#endif // INCLUDED_TODO_TYPE_SUBST_PACK_ALIAS
