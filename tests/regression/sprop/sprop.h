#ifndef INCLUDED_SPROP
#define INCLUDED_SPROP

#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>

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

struct SPropTest {
  template <typename T1> static const T1 &sFalse_rect() {
    static const T1 v = []() { throw std::logic_error("absurd case"); }();
    return v;
  }

  template <typename T1> static const T1 &sFalse_rec() {
    static const T1 v = []() { throw std::logic_error("absurd case"); }();
    return v;
  }

  template <typename t_A> struct Box {
    t_A box_value;

    __attribute__((pure)) Box<t_A> *operator->() { return this; }

    __attribute__((pure)) const Box<t_A> *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Box<t_A> clone() const {
      return Box<t_A>{clone_value((*(this)).box_value)};
    }
  };

  __attribute__((pure)) static unsigned int guarded_pred(const unsigned int &n);
  __attribute__((pure)) static unsigned int safe_div(const unsigned int &_x0,
                                                     const unsigned int &_x1);
  static inline const unsigned int test_guarded = guarded_pred(5u);
  static inline const unsigned int test_box = 42u;
  static inline const unsigned int test_div = safe_div(10u, 3u);
};

#endif // INCLUDED_SPROP
