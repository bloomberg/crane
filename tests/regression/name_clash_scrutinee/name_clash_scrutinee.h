#ifndef INCLUDED_NAME_CLASH_SCRUTINEE
#define INCLUDED_NAME_CLASH_SCRUTINEE

#include <type_traits>
#include <utility>
#include <variant>

struct NameClashScrutinee {
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

  struct shape {
    // TYPES
    struct Circle {
      uint64_t a0;
    };

    struct Square {
      uint64_t a0;
      uint64_t a1;
    };

    using variant_t = std::variant<Circle, Square>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : v_(std::move(_v)) {}

    explicit shape(Square _v) : v_(std::move(_v)) {}

    static shape circle(uint64_t a0) { return shape(Circle{a0}); }

    static shape square(uint64_t a0, uint64_t a1) {
      return shape(Square{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// Nested match: match on shape, and within a branch, match on color.
    uint64_t nested_match(Color c) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[a0] = std::get<typename shape::Circle>(this->v());
        switch (c) {
        case Color::RED: {
          return (a0 + UINT64_C(10));
        }
        case Color::GREEN: {
          return (a0 + UINT64_C(20));
        }
        case Color::BLUE: {
          return (a0 + UINT64_C(30));
        }
        default:
          std::unreachable();
        }
      } else {
        const auto &[a0, a1] = std::get<typename shape::Square>(this->v());
        switch (c) {
        case Color::RED: {
          return (a0 * a1);
        }
        case Color::GREEN: {
          return (a0 + a1);
        }
        case Color::BLUE: {
          return UINT64_C(0);
        }
        default:
          std::unreachable();
        }
      }
    }

    /// Sequential matches on different types in the same function.
    uint64_t describe(Color c) const {
      uint64_t color_val = [&]() {
        switch (c) {
        case Color::RED: {
          return UINT64_C(1);
        }
        case Color::GREEN: {
          return UINT64_C(2);
        }
        case Color::BLUE: {
          return UINT64_C(3);
        }
        default:
          std::unreachable();
        }
      }();
      uint64_t shape_val = [&]() {
        if (std::holds_alternative<typename shape::Circle>(this->v())) {
          const auto &[a0] = std::get<typename shape::Circle>(this->v());
          return a0;
        } else {
          const auto &[a0, a1] = std::get<typename shape::Square>(this->v());
          return (a0 + a1);
        }
      }();
      return (color_val + shape_val);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
    T1 shape_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[a0] = std::get<typename shape::Circle>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename shape::Square>(this->v());
        return f0(a0, a1);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
    T1 shape_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[a0] = std::get<typename shape::Circle>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename shape::Square>(this->v());
        return f0(a0, a1);
      }
    }
  };

  /// Three levels of nesting.
  struct wrapper {
    // TYPES
    struct Wrap {
      Color a0;
      shape a1;
    };

    struct Empty {};

    using variant_t = std::variant<Wrap, Empty>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    wrapper() {}

    explicit wrapper(Wrap _v) : v_(std::move(_v)) {}

    explicit wrapper(Empty _v) : v_(_v) {}

    static wrapper wrap(Color a0, shape a1) {
      return wrapper(Wrap{a0, std::move(a1)});
    }

    static wrapper empty() { return wrapper(Empty{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t triple_nest() const {
      if (std::holds_alternative<typename wrapper::Wrap>(this->v())) {
        const auto &[a0, a1] = std::get<typename wrapper::Wrap>(this->v());
        if (std::holds_alternative<typename shape::Circle>(a1.v())) {
          const auto &[a00] = std::get<typename shape::Circle>(a1.v());
          switch (a0) {
          case Color::RED: {
            return a00;
          }
          case Color::GREEN: {
            return (a00 * UINT64_C(2));
          }
          case Color::BLUE: {
            return (a00 * UINT64_C(3));
          }
          default:
            std::unreachable();
          }
        } else {
          const auto &[a00, a10] = std::get<typename shape::Square>(a1.v());
          switch (a0) {
          case Color::RED: {
            return (a00 + a10);
          }
          case Color::GREEN: {
            return (a00 * a10);
          }
          case Color::BLUE: {
            return UINT64_C(0);
          }
          default:
            std::unreachable();
          }
        }
      } else {
        return UINT64_C(0);
      }
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Color &, shape &>
  static T1 wrapper_rect(F0 &&f, T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[a0, a1] = std::get<typename wrapper::Wrap>(w.v());
      return f(a0, a1);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Color &, shape &>
  static T1 wrapper_rec(F0 &&f, T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[a0, a1] = std::get<typename wrapper::Wrap>(w.v());
      return f(a0, a1);
    } else {
      return f0;
    }
  }
};

#endif // INCLUDED_NAME_CLASH_SCRUTINEE
