#ifndef INCLUDED_TODO_DEPENDENT_FIELD_ALIAS
#define INCLUDED_TODO_DEPENDENT_FIELD_ALIAS

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
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a0, a1) } -> std::convertible_to<typename I::carrier>;
};

struct TodoDependentFieldAlias {
  using carrier = std::any;

  struct nat_magma {
    using carrier = unsigned int;

    __attribute__((pure)) static unsigned int op(unsigned int a0,
                                                 unsigned int a1) {
      return (a0 + a1);
    }
  };

  static_assert(Magma<nat_magma>);

  template <Magma _tcI0>
  __attribute__((pure)) static typename _tcI0::carrier
  pick_op(const typename _tcI0::carrier _x0,
          const typename _tcI0::carrier _x1) {
    return _tcI0::op(_x0, _x1);
  }

  static inline const unsigned int test_value = []() {
    std::function<unsigned int(unsigned int, unsigned int)> alias =
        [](unsigned int _x0, unsigned int _x1) -> unsigned int {
      return pick_op<nat_magma>(_x0, _x1);
    };
    return alias(2u, 3u);
  }();
};

#endif // INCLUDED_TODO_DEPENDENT_FIELD_ALIAS
