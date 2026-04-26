#ifndef INCLUDED_DEPENDENT_TYPENAME
#define INCLUDED_DEPENDENT_TYPENAME

#include <concepts>
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

template <typename M>
concept HasType = requires {
  typename M::t;
  requires(
      requires {
        { M::default_ } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::default_() } -> std::convertible_to<typename M::t>;
      });
};
template <typename M>
concept Container = requires { typename M::template t<void>; };

struct DependentTypename {
  template <HasType M> struct UsesType {
    static const typename M::t &get_default() {
      static const typename M::t v = M::default_;
      return v;
    }

    constexpr static typename M::t identity(const typename M::t x) { return x; }

    static const typename M::t &make_default() {
      static const typename M::t v = M::default_;
      return v;
    }
  };

  struct NatType {
    using t = unsigned int;
    static inline const t default_ = 42u;
  };

  using NatUser = UsesType<NatType>;
  static inline const NatType::t test = NatUser::get_default();

  template <Container C> struct UseContainer {
    static const typename C::template t<unsigned int> &make_nat_container() {
      static const typename C::template t<unsigned int> v =
          C::template empty<unsigned int>;
      return v;
    }

    __attribute__((pure)) static typename C::template t<unsigned int>
    use_singleton(const unsigned int &_x0) {
      return C::template singleton<unsigned int>(_x0);
    }
  };
};

#endif // INCLUDED_DEPENDENT_TYPENAME
