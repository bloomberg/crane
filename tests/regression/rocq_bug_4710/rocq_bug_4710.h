#ifndef INCLUDED_ROCQ_BUG_4710
#define INCLUDED_ROCQ_BUG_4710

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

struct RocqBug4710 {
  struct Foo_ {
    unsigned int foo;

    __attribute__((pure)) Foo_ *operator->() { return this; }

    __attribute__((pure)) const Foo_ *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Foo_ clone() const { return Foo_{(*(this)).foo}; }
  };

  struct Foo2 {
    unsigned int foo2p;
    bool foo2b;

    __attribute__((pure)) Foo2 *operator->() { return this; }

    __attribute__((pure)) const Foo2 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Foo2 clone() const {
      return Foo2{(*(this)).foo2p, (*(this)).foo2b};
    }
  };

  __attribute__((pure)) static unsigned int bla(const Foo2 &x);
  __attribute__((pure)) static bool bla_(const unsigned int &_x, const Foo2 &x);
  static inline const Foo_ test_foo = Foo_{5u};
  static inline const Foo2 test_foo2 = Foo2{10u, true};
  static inline const unsigned int test_bla = bla(test_foo2);
  static inline const bool test_bla_ = bla_(0u, test_foo2);
};

#endif // INCLUDED_ROCQ_BUG_4710
