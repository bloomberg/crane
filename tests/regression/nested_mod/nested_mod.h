#ifndef INCLUDED_NESTED_MOD
#define INCLUDED_NESTED_MOD

#include <type_traits>
#include <utility>
#include <variant>

struct NestedMod {
  struct Outer {
    enum class Color { RED, GREEN, BLUE };

    template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
      switch (c) {
      case Color::RED: {
        return f;
      }
      case Color::GREEN: {
        return f0;
      }
      case Color::BLUE: {
        return f1;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
      switch (c) {
      case Color::RED: {
        return f;
      }
      case Color::GREEN: {
        return f0;
      }
      case Color::BLUE: {
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
          unsigned int a0;
        };

        struct Square {
          unsigned int a0;
        };

        struct Triangle {
          unsigned int a0;
          unsigned int a1;
          unsigned int a2;
        };

        using variant_t = std::variant<Circle, Square, Triangle>;

      private:
        // DATA
        variant_t v_;

      public:
        // CREATORS
        shape() {}

        explicit shape(Circle _v) : v_(std::move(_v)) {}

        explicit shape(Square _v) : v_(std::move(_v)) {}

        explicit shape(Triangle _v) : v_(std::move(_v)) {}

        shape(const shape &_other) : v_(std::move(_other.clone().v_)) {}

        shape(shape &&_other) noexcept : v_(std::move(_other.v_)) {}

        shape &operator=(const shape &_other) {
          v_ = std::move(_other.clone().v_);
          return *this;
        }

        shape &operator=(shape &&_other) noexcept {
          v_ = std::move(_other.v_);
          return *this;
        }

        // ACCESSORS
        shape clone() const {
          if (std::holds_alternative<Circle>(this->v())) {
            const auto &[a0] = std::get<Circle>(this->v());
            return shape(Circle{a0});
          } else if (std::holds_alternative<Square>(this->v())) {
            const auto &[a0] = std::get<Square>(this->v());
            return shape(Square{a0});
          } else {
            const auto &[a0, a1, a2] = std::get<Triangle>(this->v());
            return shape(Triangle{a0, a1, a2});
          }
        }

        // CREATORS
        static shape circle(unsigned int a0) { return shape(Circle{a0}); }

        static shape square(unsigned int a0) { return shape(Square{a0}); }

        static shape triangle(unsigned int a0, unsigned int a1,
                              unsigned int a2) {
          return shape(Triangle{a0, a1, a2});
        }

        // MANIPULATORS
        inline variant_t &v_mut() { return v_; }

        // ACCESSORS
        const variant_t &v() const { return v_; }
      };

      template <typename T1, typename F0, typename F1, typename F2>
        requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
                 std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
                 std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int &,
                                       unsigned int &>
      static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
        if (std::holds_alternative<typename shape::Circle>(s.v())) {
          const auto &[a0] = std::get<typename shape::Circle>(s.v());
          return f(a0);
        } else if (std::holds_alternative<typename shape::Square>(s.v())) {
          const auto &[a0] = std::get<typename shape::Square>(s.v());
          return f0(a0);
        } else {
          const auto &[a0, a1, a2] = std::get<typename shape::Triangle>(s.v());
          return f1(a0, a1, a2);
        }
      }

      template <typename T1, typename F0, typename F1, typename F2>
        requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
                 std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
                 std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int &,
                                       unsigned int &>
      static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
        if (std::holds_alternative<typename shape::Circle>(s.v())) {
          const auto &[a0] = std::get<typename shape::Circle>(s.v());
          return f(a0);
        } else if (std::holds_alternative<typename shape::Square>(s.v())) {
          const auto &[a0] = std::get<typename shape::Square>(s.v());
          return f0(a0);
        } else {
          const auto &[a0, a1, a2] = std::get<typename shape::Triangle>(s.v());
          return f1(a0, a1, a2);
        }
      }

      static unsigned int area(const shape &s);
    };

    static unsigned int shape_with_color(const Inner::shape &s, Color c);
    static unsigned int color_code(Color c);
  };

  static inline const Outer::Inner::shape my_circle =
      Outer::Inner::shape::circle(5u);
  static inline const Outer::Color my_color = Outer::Color::RED;
  static inline const unsigned int test_area = Outer::Inner::area(my_circle);
  static inline const unsigned int test_combined =
      Outer::shape_with_color(my_circle, my_color);
  static inline const unsigned int test_color = Outer::color_code(my_color);
};

#endif // INCLUDED_NESTED_MOD
