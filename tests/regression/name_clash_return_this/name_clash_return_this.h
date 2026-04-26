#ifndef INCLUDED_NAME_CLASH_RETURN_THIS
#define INCLUDED_NAME_CLASH_RETURN_THIS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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

struct NameClashReturnThis {
  /// Test: match-as-expression where one branch returns the scrutinee itself.
  /// When methodified, this becomes `return this` which is a raw pointer,
  /// but the IIFE lambda expects shared_ptr.
  struct shape {
    // TYPES
    struct Circle {
      unsigned int d_a0;
    };

    struct Square {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<Circle, Square>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    shape(const shape &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    shape(shape &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) shape &operator=(const shape &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) shape &operator=(shape &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) shape clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<Circle>(_sv.v());
        return shape(Circle{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<Square>(_sv.v());
        return shape(Square{d_a0, d_a1});
      }
    }

    // CREATORS
    __attribute__((pure)) static shape circle(unsigned int a0) {
      return shape(Circle{std::move(a0)});
    }

    __attribute__((pure)) static shape square(unsigned int a0,
                                              unsigned int a1) {
      return shape(Square{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) shape *operator->() { return this; }

    __attribute__((pure)) const shape *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = shape(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 shape_rect(F0 &&f, F1 &&f0, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename shape::Square>(s.v());
      return f0(d_a0, d_a1);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 shape_rec(F0 &&f, F1 &&f0, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename shape::Square>(s.v());
      return f0(d_a0, d_a1);
    }
  }

  /// Inner match returns shape in all branches, one branch returns the
  /// argument itself. The function takes shape as input, so it gets
  /// methodified. In the Blue branch, `s` becomes `this`.
  __attribute__((pure)) static shape maybe_transform(const bool &flag, shape s);
  /// Match on shape where one branch returns the same shape unchanged.
  __attribute__((pure)) static shape identity_or_double(const shape &s);
  /// Two shapes, return one of them based on a match on the other.
  __attribute__((pure)) static shape pick_shape(shape s1, shape s2);
  /// Nested: match on result of a function that may return this
  __attribute__((pure)) static unsigned int nested_this(const shape &s);
};

#endif // INCLUDED_NAME_CLASH_RETURN_THIS
