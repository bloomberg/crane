#ifndef INCLUDED_CTOR_ESCAPE_COLLISION
#define INCLUDED_CTOR_ESCAPE_COLLISION

#include <memory>
#include <optional>
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

struct CtorEscapeCollision {
  enum class Item { e_D_, e_D_0, e_D__, e_D__0, e_D__1, e_D__2 };

  template <typename T1>
  static T1 item_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const T1 f4, const Item i) {
    switch (i) {
    case Item::e_D_: {
      return f;
    }
    case Item::e_D_0: {
      return f0;
    }
    case Item::e_D__: {
      return f1;
    }
    case Item::e_D__0: {
      return f2;
    }
    case Item::e_D__1: {
      return f3;
    }
    case Item::e_D__2: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 item_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                     const T1 f3, const T1 f4, const Item i) {
    switch (i) {
    case Item::e_D_: {
      return f;
    }
    case Item::e_D_0: {
      return f0;
    }
    case Item::e_D__: {
      return f1;
    }
    case Item::e_D__0: {
      return f2;
    }
    case Item::e_D__1: {
      return f3;
    }
    case Item::e_D__2: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int tag(const Item x);
  static inline const unsigned int t =
      (((((tag(Item::e_D_) + tag(Item::e_D_0)) + tag(Item::e_D__)) +
         tag(Item::e_D__0)) +
        tag(Item::e_D__1)) +
       tag(Item::e_D__2));
};

#endif // INCLUDED_CTOR_ESCAPE_COLLISION
