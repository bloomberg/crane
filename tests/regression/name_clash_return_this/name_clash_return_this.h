#ifndef INCLUDED_NAME_CLASH_RETURN_THIS
#define INCLUDED_NAME_CLASH_RETURN_THIS

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
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 shape_rect(F0 &&f, F1 &&f0, const std::shared_ptr<shape> &s) {
    if (std::holds_alternative<typename shape::Circle>(s->v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s->v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename shape::Square>(s->v());
      return f0(d_a0, d_a1);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 shape_rec(F0 &&f, F1 &&f0, const std::shared_ptr<shape> &s) {
    if (std::holds_alternative<typename shape::Circle>(s->v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s->v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename shape::Square>(s->v());
      return f0(d_a0, d_a1);
    }
  }

  /// Inner match returns shape in all branches, one branch returns the
  /// argument itself. The function takes shape as input, so it gets
  /// methodified. In the Blue branch, `s` becomes `this`.
  static std::shared_ptr<shape> maybe_transform(const bool flag,
                                                std::shared_ptr<shape> s);
  /// Match on shape where one branch returns the same shape unchanged.
  static std::shared_ptr<shape>
  identity_or_double(const std::shared_ptr<shape> &s);
  /// Two shapes, return one of them based on a match on the other.
  static std::shared_ptr<shape> pick_shape(std::shared_ptr<shape> s1,
                                           std::shared_ptr<shape> s2);
  /// Nested: match on result of a function that may return this
  __attribute__((pure)) static unsigned int
  nested_this(const std::shared_ptr<shape> &s);
};

#endif // INCLUDED_NAME_CLASH_RETURN_THIS
