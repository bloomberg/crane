#ifndef INCLUDED_FIX_IN_RECORD
#define INCLUDED_FIX_IN_RECORD

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

struct FixInRecord {
  /// A local fixpoint stored in a Rocq record field.
  ///
  /// BUG HYPOTHESIS: Records are translated to C++ structs with named
  /// fields. A field of type nat -> nat becomes
  /// std::function<unsigned int(unsigned int)>. When a local fixpoint
  /// (which uses & capture) is stored in a record field, the
  /// std::function wraps the & closure. After the creating function
  /// returns, the captured references dangle.
  ///
  /// This is a different escape mechanism from option/pair/list:
  /// the closure escapes through a RECORD FIELD.
  struct fn_box {
    unsigned int label;
    std::function<unsigned int(unsigned int)> fn;

    __attribute__((pure)) fn_box *operator->() { return this; }

    __attribute__((pure)) const fn_box *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) fn_box clone() const {
      return fn_box{(*(this)).label, (*(this)).fn};
    }
  };

  __attribute__((pure)) static fn_box make_box(const unsigned int &n);
  /// test1: n=10, base=30, fn = add where add(x) = 30+x.
  /// fn(make_box 10)(7) = 30 + 7 = 37.
  /// Bug: base captured by & in add, dangles after make_box returns.
  static inline const unsigned int test1 = make_box(10u).fn(7u);
  /// test2: With intervening work.
  /// n=20, base=60, fn(5) = 60+5 = 65.
  static inline const unsigned int test2 = []() {
    fn_box bx = make_box(20u);
    unsigned int noise = ((((1u + 2u) + 3u) + 4u) + 5u);
    return bx.fn(noise);
  }();
  /// test3: Use label too (to ensure struct is alive).
  /// n=5, base=15, label=15, fn(0) = 15. label + fn(0) = 30.
  static inline const unsigned int test3 = []() {
    fn_box bx = make_box(5u);
    return (bx.label + bx.fn(0u));
  }();
};

#endif // INCLUDED_FIX_IN_RECORD
