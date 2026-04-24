#ifndef INCLUDED_NESTED_MOD
#define INCLUDED_NESTED_MOD

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

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct NestedMod {
  struct Outer {
    enum class Color { e_RED, e_GREEN, e_BLUE };

    template <typename T1>
    static T1 color_rect(const T1 f, const T1 f0, const T1 f1, const Color c) {
      switch (c) {
      case Color::e_RED: {
        return f;
      }
      case Color::e_GREEN: {
        return f0;
      }
      case Color::e_BLUE: {
        return f1;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1>
    static T1 color_rec(const T1 f, const T1 f0, const T1 f1, const Color c) {
      switch (c) {
      case Color::e_RED: {
        return f;
      }
      case Color::e_GREEN: {
        return f0;
      }
      case Color::e_BLUE: {
        return f1;
      }
      default:
        std::unreachable();
      }
    }

    struct Inner {
      struct shape {
        // TYPES
        struct Circle {
          unsigned int d_a0;
        };

        struct Square {
          unsigned int d_a0;
        };

        struct Triangle {
          unsigned int d_a0;
          unsigned int d_a1;
          unsigned int d_a2;
        };

        using variant_t = std::variant<Circle, Square, Triangle>;

      private:
        // DATA
        variant_t d_v_;

      public:
        // CREATORS
        shape() {}

        explicit shape(Circle _v) : d_v_(std::move(_v)) {}

        explicit shape(Square _v) : d_v_(std::move(_v)) {}

        explicit shape(Triangle _v) : d_v_(std::move(_v)) {}

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
            return shape(Circle{clone_as_value<unsigned int>(d_a0)});
          } else if (std::holds_alternative<Square>(_sv.v())) {
            const auto &[d_a0] = std::get<Square>(_sv.v());
            return shape(Square{clone_as_value<unsigned int>(d_a0)});
          } else {
            const auto &[d_a0, d_a1, d_a2] = std::get<Triangle>(_sv.v());
            return shape(Triangle{clone_as_value<unsigned int>(d_a0),
                                  clone_as_value<unsigned int>(d_a1),
                                  clone_as_value<unsigned int>(d_a2)});
          }
        }

        // CREATORS
        __attribute__((pure)) static shape circle(unsigned int a0) {
          return shape(Circle{std::move(a0)});
        }

        __attribute__((pure)) static shape square(unsigned int a0) {
          return shape(Square{std::move(a0)});
        }

        __attribute__((pure)) static shape
        triangle(unsigned int a0, unsigned int a1, unsigned int a2) {
          return shape(Triangle{std::move(a0), std::move(a1), std::move(a2)});
        }

        // MANIPULATORS
        __attribute__((pure)) variant_t &v_mut() { return d_v_; }

        // ACCESSORS
        __attribute__((pure)) shape *operator->() { return this; }

        __attribute__((pure)) const shape *operator->() const { return this; }

        __attribute__((pure)) bool operator!=(std::nullptr_t) const {
          return true;
        }

        __attribute__((pure)) bool operator==(std::nullptr_t) const {
          return false;
        }

        // MANIPULATORS
        void reset() { *this = shape(); }

        // ACCESSORS
        __attribute__((pure)) const variant_t &v() const { return d_v_; }
      };

      template <typename T1, MapsTo<T1, unsigned int> F0,
                MapsTo<T1, unsigned int> F1,
                MapsTo<T1, unsigned int, unsigned int, unsigned int> F2>
      static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
        if (std::holds_alternative<typename shape::Circle>(s.v())) {
          const auto &[d_a0] = std::get<typename shape::Circle>(s.v());
          return f(d_a0);
        } else if (std::holds_alternative<typename shape::Square>(s.v())) {
          const auto &[d_a0] = std::get<typename shape::Square>(s.v());
          return f0(d_a0);
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename shape::Triangle>(s.v());
          return f1(d_a0, d_a1, d_a2);
        }
      }

      template <typename T1, MapsTo<T1, unsigned int> F0,
                MapsTo<T1, unsigned int> F1,
                MapsTo<T1, unsigned int, unsigned int, unsigned int> F2>
      static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
        if (std::holds_alternative<typename shape::Circle>(s.v())) {
          const auto &[d_a0] = std::get<typename shape::Circle>(s.v());
          return f(d_a0);
        } else if (std::holds_alternative<typename shape::Square>(s.v())) {
          const auto &[d_a0] = std::get<typename shape::Square>(s.v());
          return f0(d_a0);
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename shape::Triangle>(s.v());
          return f1(d_a0, d_a1, d_a2);
        }
      }

      __attribute__((pure)) static unsigned int area(const shape &s);
    };

    __attribute__((pure)) static unsigned int
    shape_with_color(const Inner::shape &s, const Color c);
    __attribute__((pure)) static unsigned int color_code(const Color c);
  };

  static inline const Outer::Inner::shape my_circle =
      Outer::Inner::shape::circle(5u);
  static inline const Outer::Color my_color = Outer::Color::e_RED;
  static inline const unsigned int test_area = Outer::Inner::area(my_circle);
  static inline const unsigned int test_combined =
      Outer::shape_with_color(my_circle, my_color);
  static inline const unsigned int test_color = Outer::color_code(my_color);
};

#endif // INCLUDED_NESTED_MOD
