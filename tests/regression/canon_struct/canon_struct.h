#ifndef INCLUDED_CANON_STRUCT
#define INCLUDED_CANON_STRUCT

#include <any>
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

struct Bool {
  __attribute__((pure)) static bool eqb(const bool &b1, const bool &b2);
};

template <typename I>
concept EqType = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::eqb(a0, a1) } -> std::convertible_to<bool>;
};

struct CanonStruct {
  using carrier = std::any;

  struct nat_eqType {
    using carrier = unsigned int;

    __attribute__((pure)) static bool eqb(unsigned int a0, unsigned int a1) {
      return a0 == a1;
    }
  };

  static_assert(EqType<nat_eqType>);

  struct bool_eqType {
    using carrier = bool;

    constexpr static bool eqb(bool a0, bool a1) { return Bool::eqb(a0, a1); }
  };

  static_assert(EqType<bool_eqType>);

  template <EqType _tcI0>
  __attribute__((pure)) static bool same(const typename _tcI0::carrier x,
                                         const typename _tcI0::carrier y) {
    return _tcI0::eqb(x, y);
  }

  static inline const bool test_nat = same<nat_eqType>(3u, 5u);
  static inline const bool test_bool = same<bool_eqType>(true, false);
};

#endif // INCLUDED_CANON_STRUCT
