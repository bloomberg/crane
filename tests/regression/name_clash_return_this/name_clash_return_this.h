#ifndef INCLUDED_NAME_CLASH_RETURN_THIS
#define INCLUDED_NAME_CLASH_RETURN_THIS

#include <type_traits>
#include <utility>
#include <variant>

struct NameClashReturnThis {
  /// Test: match-as-expression where one branch returns the scrutinee itself.
  /// When methodified, this becomes `return this` which is a raw pointer,
  /// but the IIFE lambda expects shared_ptr.
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
      } else {
        const auto &[a0, a1] = std::get<Square>(this->v());
        return shape(Square{a0, a1});
      }
    }

    // CREATORS
    static shape circle(uint64_t a0) { return shape(Circle{a0}); }

    static shape square(uint64_t a0, uint64_t a1) {
      return shape(Square{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
  static T1 shape_rect(F0 &&f, F1 &&f0, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[a0] = std::get<typename shape::Circle>(s.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename shape::Square>(s.v());
      return f0(a0, a1);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
  static T1 shape_rec(F0 &&f, F1 &&f0, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[a0] = std::get<typename shape::Circle>(s.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename shape::Square>(s.v());
      return f0(a0, a1);
    }
  }

  /// Inner match returns shape in all branches, one branch returns the
  /// argument itself. The function takes shape as input, so it gets
  /// methodified. In the Blue branch, `s` becomes `this`.
  static shape maybe_transform(bool flag, shape s);
  /// Match on shape where one branch returns the same shape unchanged.
  static shape identity_or_double(const shape &s);
  /// Two shapes, return one of them based on a match on the other.
  static shape pick_shape(shape s1, shape s2);
  /// Nested: match on result of a function that may return this
  static uint64_t nested_this(const shape &s);
};

#endif // INCLUDED_NAME_CLASH_RETURN_THIS
