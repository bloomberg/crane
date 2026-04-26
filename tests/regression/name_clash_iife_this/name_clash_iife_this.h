#ifndef INCLUDED_NAME_CLASH_IIFE_THIS
#define INCLUDED_NAME_CLASH_IIFE_THIS

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

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
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
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
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
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
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

  __attribute__((pure)) static unsigned int match_of_match(const Color c,
                                                           const shape &s);

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

    __attribute__((pure)) wrapper &operator=(const wrapper &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) wrapper &operator=(wrapper &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) wrapper clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Wrap>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Wrap>(_sv.v());
        return wrapper(Wrap{d_a0, d_a1});
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

#endif // INCLUDED_NAME_CLASH_IIFE_THIS
