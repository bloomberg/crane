#ifndef INCLUDED_NAME_CLASH_IIFE_THIS
#define INCLUDED_NAME_CLASH_IIFE_THIS

#include <type_traits>
#include <utility>
#include <variant>

struct NameClashIifeThis {
  enum class Color { e_RED, e_GREEN, e_BLUE };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
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

  template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
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
      if (std::holds_alternative<Circle>(this->v())) {
        const auto &[d_a0] = std::get<Circle>(this->v());
        return shape(Circle{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<Square>(this->v());
        return shape(Square{d_a0, d_a1});
      }
    }

    // CREATORS
    static shape circle(unsigned int a0) { return shape(Circle{a0}); }

    static shape square(unsigned int a0, unsigned int a1) {
      return shape(Square{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int nested_match(Color c) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(this->v());
        switch (c) {
        case Color::e_RED: {
          return (d_a0 + 10u);
        }
        case Color::e_GREEN: {
          return (d_a0 + 20u);
        }
        case Color::e_BLUE: {
          return (d_a0 + 30u);
        }
        default:
          std::unreachable();
        }
      } else {
        const auto &[d_a0, d_a1] = std::get<typename shape::Square>(this->v());
        switch (c) {
        case Color::e_RED: {
          return (d_a0 * d_a1);
        }
        case Color::e_GREEN: {
          return (d_a0 + d_a1);
        }
        case Color::e_BLUE: {
          return 0u;
        }
        default:
          std::unreachable();
        }
      }
    }

    unsigned int describe(Color c) const {
      unsigned int color_val = [&]() {
        switch (c) {
        case Color::e_RED: {
          return 1u;
        }
        case Color::e_GREEN: {
          return 2u;
        }
        case Color::e_BLUE: {
          return 3u;
        }
        default:
          std::unreachable();
        }
      }();
      unsigned int shape_val = [&]() {
        if (std::holds_alternative<typename shape::Circle>(this->v())) {
          const auto &[d_a0] = std::get<typename shape::Circle>(this->v());
          return d_a0;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename shape::Square>(this->v());
          return (d_a0 + d_a1);
        }
      }();
      return (color_val + shape_val);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &, unsigned int &>
    T1 shape_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(this->v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename shape::Square>(this->v());
        return f0(d_a0, d_a1);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &, unsigned int &>
    T1 shape_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(this->v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename shape::Square>(this->v());
        return f0(d_a0, d_a1);
      }
    }
  };

  static unsigned int match_of_match(Color c, const shape &s);

  struct wrapper {
    // TYPES
    struct Wrap {
      Color d_a0;
      shape d_a1;
    };

    struct Empty {};

    using variant_t = std::variant<Wrap, Empty>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    wrapper() {}

    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    explicit wrapper(Empty _v) : d_v_(_v) {}

    wrapper(const wrapper &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    wrapper(wrapper &&_other) : d_v_(std::move(_other.d_v_)) {}

    wrapper &operator=(const wrapper &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    wrapper &operator=(wrapper &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    wrapper clone() const {
      if (std::holds_alternative<Wrap>(this->v())) {
        const auto &[d_a0, d_a1] = std::get<Wrap>(this->v());
        return wrapper(Wrap{d_a0, d_a1.clone()});
      } else {
        return wrapper(Empty{});
      }
    }

    // CREATORS
    static wrapper wrap(Color a0, shape a1) {
      return wrapper(Wrap{a0, std::move(a1)});
    }

    static wrapper empty() { return wrapper(Empty{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int triple_nest() const {
      if (std::holds_alternative<typename wrapper::Wrap>(this->v())) {
        const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(this->v());
        if (std::holds_alternative<typename shape::Circle>(d_a1.v())) {
          const auto &[d_a00] = std::get<typename shape::Circle>(d_a1.v());
          switch (d_a0) {
          case Color::e_RED: {
            return d_a00;
          }
          case Color::e_GREEN: {
            return (d_a00 * 2u);
          }
          case Color::e_BLUE: {
            return (d_a00 * 3u);
          }
          default:
            std::unreachable();
          }
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename shape::Square>(d_a1.v());
          switch (d_a0) {
          case Color::e_RED: {
            return (d_a00 + d_a10);
          }
          case Color::e_GREEN: {
            return (d_a00 * d_a10);
          }
          case Color::e_BLUE: {
            return 0u;
          }
          default:
            std::unreachable();
          }
        }
      } else {
        return 0u;
      }
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Color &, shape &>
  static T1 wrapper_rect(F0 &&f, T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(w.v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Color &, shape &>
  static T1 wrapper_rec(F0 &&f, T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(w.v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }
};

#endif // INCLUDED_NAME_CLASH_IIFE_THIS
