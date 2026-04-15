#ifndef INCLUDED_NAME_CLASH_IIFE_THIS
#define INCLUDED_NAME_CLASH_IIFE_THIS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct NameClashIifeThis {
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
    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<shape> circle(unsigned int a0) {
      return std::make_shared<shape>(Circle{std::move(a0)});
    }

    static std::shared_ptr<shape> square(unsigned int a0, unsigned int a1) {
      return std::make_shared<shape>(Square{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int nested_match(const Color c) const {
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

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, unsigned int> F1>
    T1 shape_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(this->v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename shape::Square>(this->v());
        return f0(d_a0, d_a1);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, unsigned int> F1>
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

  __attribute__((pure)) static unsigned int
  match_of_match(const Color c, const std::shared_ptr<shape> &s);

  struct wrapper {
    // TYPES
    struct Wrap {
      Color d_a0;
      std::shared_ptr<shape> d_a1;
    };

    struct Empty {};

    using variant_t = std::variant<Wrap, Empty>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    explicit wrapper(Empty _v) : d_v_(_v) {}

    static std::shared_ptr<wrapper> wrap(Color a0,
                                         const std::shared_ptr<shape> &a1) {
      return std::make_shared<wrapper>(Wrap{std::move(a0), a1});
    }

    static std::shared_ptr<wrapper> wrap(Color a0,
                                         std::shared_ptr<shape> &&a1) {
      return std::make_shared<wrapper>(Wrap{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<wrapper> empty() {
      return std::make_shared<wrapper>(Empty{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int triple_nest() const {
      if (std::holds_alternative<typename wrapper::Wrap>(this->v())) {
        const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(this->v());
        if (std::holds_alternative<typename shape::Circle>(d_a1->v())) {
          const auto &[d_a00] = std::get<typename shape::Circle>(d_a1->v());
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
              std::get<typename shape::Square>(d_a1->v());
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

  template <typename T1, MapsTo<T1, Color, std::shared_ptr<shape>> F0>
  static T1 wrapper_rect(F0 &&f, const T1 f0,
                         const std::shared_ptr<wrapper> &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w->v())) {
      const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(w->v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, Color, std::shared_ptr<shape>> F0>
  static T1 wrapper_rec(F0 &&f, const T1 f0,
                        const std::shared_ptr<wrapper> &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w->v())) {
      const auto &[d_a0, d_a1] = std::get<typename wrapper::Wrap>(w->v());
      return f(d_a0, d_a1);
    } else {
      return f0;
    }
  }
};

#endif // INCLUDED_NAME_CLASH_IIFE_THIS
