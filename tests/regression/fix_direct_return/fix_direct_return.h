#ifndef INCLUDED_FIX_DIRECT_RETURN
#define INCLUDED_FIX_DIRECT_RETURN

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

struct FixDirectReturn {
  /// A local fixpoint is captured by an outer lambda and returned.
  /// Crane can't uncurry here because the fixpoint is used as a VALUE
  /// inside the returned lambda (not fully applied at the return site).
  ///
  /// BUG: The inner fixpoint add uses & capture. Even though the
  /// outer lambda uses = capture (via return_captures_by_value),
  /// the COPY of add (a std::function) inside the outer lambda
  /// still holds & references to the destroyed stack variables.
  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  make_callback(const unsigned int &base, F1 &&_x0) {
    return [=]() mutable {
      auto add = std::make_shared<std::function<unsigned int(unsigned int)>>();
      *add = [=](unsigned int x) mutable -> unsigned int {
        if (x <= 0) {
          return base;
        } else {
          unsigned int x_ = x - 1;
          return ((*add)(x_) + 1);
        }
      };
      return [=](const std::function<unsigned int(unsigned int)> g) mutable {
        return (g((*add)(0u)) + (*add)(1u));
      };
    }()(_x0);
  }

  /// test1: make_callback(42)(fun x => x) = id(42) + 43 = 85.
  static inline const unsigned int test1 =
      make_callback(42u, [](unsigned int x) { return x; });
  /// test2: make_callback(10)(fun x => x * 2) = 20 + 11 = 31.
  static inline const unsigned int test2 =
      make_callback(10u, [](const unsigned int &x) { return (x * 2u); });
  /// test3: Nested — use the closure from make_callback inside another
  /// make_callback.
  static inline const unsigned int test3 = []() {
    return []() {
      std::function<unsigned int(std::function<unsigned int(unsigned int)>)>
          cb1 = [](std::function<unsigned int(unsigned int)> _x0)
          -> unsigned int { return make_callback(5u, _x0); };
      std::function<unsigned int(std::function<unsigned int(unsigned int)>)>
          cb2 = [](std::function<unsigned int(unsigned int)> _x0)
          -> unsigned int { return make_callback(100u, _x0); };
      return cb1([=](const unsigned int &) mutable {
        return cb2([](unsigned int x) { return x; });
      });
    }();
  }();
};

#endif // INCLUDED_FIX_DIRECT_RETURN
