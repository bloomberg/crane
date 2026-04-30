#ifndef INCLUDED_NESTED_MOD
#define INCLUDED_NESTED_MOD

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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

        shape &operator=(const shape &_other) {
          d_v_ = std::move(_other.clone().d_v_);
          return *this;
        }

        shape &operator=(shape &&_other) {
          d_v_ = std::move(_other.d_v_);
          return *this;
        }

        // ACCESSORS
        shape clone() const {
          auto &&_sv = *(this);
          if (std::holds_alternative<Circle>(_sv.v())) {
            const auto &[d_a0] = std::get<Circle>(_sv.v());
            return shape(Circle{d_a0});
          } else if (std::holds_alternative<Square>(_sv.v())) {
            const auto &[d_a0] = std::get<Square>(_sv.v());
            return shape(Square{d_a0});
          } else {
            const auto &[d_a0, d_a1, d_a2] = std::get<Triangle>(_sv.v());
            return shape(Triangle{d_a0, d_a1, d_a2});
          }
        }

        // CREATORS
        static shape circle(unsigned int a0) {
          return shape(Circle{std::move(a0)});
        }

        static shape square(unsigned int a0) {
          return shape(Square{std::move(a0)});
        }

        static shape triangle(unsigned int a0, unsigned int a1,
                              unsigned int a2) {
          return shape(Triangle{std::move(a0), std::move(a1), std::move(a2)});
        }

        // MANIPULATORS
        inline variant_t &v_mut() { return d_v_; }

        // ACCESSORS
        const variant_t &v() const { return d_v_; }
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

      static unsigned int area(const shape &s);
    };

    static unsigned int shape_with_color(const Inner::shape &s, const Color c);
    static unsigned int color_code(const Color c);
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
