#ifndef INCLUDED_NAME_CLASH_SCRUTINEE
#define INCLUDED_NAME_CLASH_SCRUTINEE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NameClashScrutinee {
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

    /// Nested match: match on shape, and within a branch, match on color.
    __attribute__((pure)) unsigned int nested_match(const Color c) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename shape::Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(_sv.v());
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
        const auto &[d_a0, d_a1] = std::get<typename shape::Square>(_sv.v());
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

    /// Sequential matches on different types in the same function.
    __attribute__((pure)) unsigned int describe(const Color c) const {
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
        auto &&_sv = *(this);
        if (std::holds_alternative<typename shape::Circle>(_sv.v())) {
          const auto &[d_a0] = std::get<typename shape::Circle>(_sv.v());
          return d_a0;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename shape::Square>(_sv.v());
          return (d_a0 + d_a1);
        }
      }();
      return (color_val + shape_val);
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, unsigned int> F1>
    T1 shape_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename shape::Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename shape::Square>(_sv.v());
        return f0(d_a0, d_a1);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, unsigned int> F1>
    T1 shape_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename shape::Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename shape::Square>(_sv.v());
        return f0(d_a0, d_a1);
      }
    }
  };

  /// Three levels of nesting.
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
    __attribute__((pure)) wrapper clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Wrap>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Wrap>(_sv.v());
        return wrapper(Wrap{d_a0, d_a1.clone()});
      } else {
        return wrapper(Empty{});
      }
    }

    // CREATORS
    constexpr static wrapper wrap(Color a0, shape a1) {
      return wrapper(Wrap{std::move(a0), std::move(a1)});
    }

    constexpr static wrapper empty() { return wrapper(Empty{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) wrapper *operator->() { return this; }

    __attribute__((pure)) const wrapper *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = wrapper(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int triple_nest() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename wrapper::Wrap>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(_sv.v());
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

  template <typename T1, MapsTo<T1, Color, shape> F0>
  static T1 wrapper_rect(F0 &&f, const T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(w.v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, Color, shape> F0>
  static T1 wrapper_rec(F0 &&f, const T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(w.v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }
};

#endif // INCLUDED_NAME_CLASH_SCRUTINEE
