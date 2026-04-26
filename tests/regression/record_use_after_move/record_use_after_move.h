#ifndef INCLUDED_RECORD_USE_AFTER_MOVE
#define INCLUDED_RECORD_USE_AFTER_MOVE

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

struct RecordUseAfterMove {
  struct box {
    unsigned int payload;
    bool enabled;

    __attribute__((pure)) box *operator->() { return this; }

    __attribute__((pure)) const box *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) box clone() const {
      return box{(*(this)).payload, (*(this)).enabled};
    }
  };

  __attribute__((pure)) static box clone_box(const box &b);
  __attribute__((pure)) static box keep_box(box b);
  __attribute__((pure)) static unsigned int use_box(const box &b);
  static inline const box initial_box = box{41u, true};
  /// BUG: The same shared_ptr local b is moved into multiple call sites.
  /// After the first std::move(b), subsequent uses dereference a
  /// moved-from shared_ptr, causing a segfault.
  static inline const box problematic = []() {
    box b = keep_box(initial_box);
    box b1 = clone_box(b);
    box b2 = clone_box(b);
    if (keep_box(b).enabled) {
      if (b.enabled) {
        return b2;
      } else {
        return b1;
      }
    } else {
      return b1;
    }
  }();
  /// Simple case: same record used twice in let bindings.
  static inline const unsigned int double_let = []() {
    unsigned int x = initial_box.payload;
    unsigned int y = initial_box.payload;
    return (x + y);
  }();
  /// Record passed to two different functions.
  static inline const unsigned int two_consumers = []() {
    unsigned int p = use_box(initial_box);
    unsigned int q = use_box(initial_box);
    return (p + q);
  }();
};

#endif // INCLUDED_RECORD_USE_AFTER_MOVE
