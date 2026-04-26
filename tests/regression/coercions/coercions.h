#ifndef INCLUDED_COERCIONS
#define INCLUDED_COERCIONS

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

struct Coercions {
  __attribute__((pure)) static unsigned int bool_to_nat(const bool &b);
  __attribute__((pure)) static unsigned int add_bool(const unsigned int &n,
                                                     const bool &b);
  static inline const unsigned int test_add_true = add_bool(5u, true);
  static inline const unsigned int test_add_false = add_bool(5u, false);

  struct Wrapper {
    unsigned int unwrap;

    __attribute__((pure)) Wrapper *operator->() { return this; }

    __attribute__((pure)) const Wrapper *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Wrapper clone() const {
      return Wrapper{(*(this)).unwrap};
    }
  };

  __attribute__((pure)) static unsigned int double_wrapped(const Wrapper &w);
  static inline const unsigned int test_double_wrapped =
      double_wrapped(Wrapper{7u});

  struct BoolBox {
    bool unbox;

    __attribute__((pure)) BoolBox *operator->() { return this; }

    __attribute__((pure)) const BoolBox *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) BoolBox clone() const {
      return BoolBox{(*(this)).unbox};
    }
  };

  __attribute__((pure)) static unsigned int add_boolbox(const unsigned int &n,
                                                        const BoolBox &bb);
  static inline const unsigned int test_add_boolbox =
      add_boolbox(10u, BoolBox{true});

  struct Transform {
    std::function<unsigned int(unsigned int)> apply_transform;

    __attribute__((pure)) Transform *operator->() { return this; }

    __attribute__((pure)) const Transform *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Transform clone() const {
      return Transform{(*(this)).apply_transform};
    }
  };

  static inline const Transform double_transform =
      Transform{[](const unsigned int &n) { return (n + n); }};
  static inline const unsigned int test_fun_coercion =
      double_transform.apply_transform(5u);
};

#endif // INCLUDED_COERCIONS
