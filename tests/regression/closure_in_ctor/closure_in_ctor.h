#ifndef INCLUDED_CLOSURE_IN_CTOR
#define INCLUDED_CLOSURE_IN_CTOR

#include <functional>
#include <type_traits>
#include <utility>
#include <variant>

struct ClosureInCtor {
  struct box {
    // TYPES
    struct Box0 {
      std::function<uint64_t(uint64_t)> a0;
    };

    struct Empty {};

    using variant_t = std::variant<Box0, Empty>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    box() {}

    explicit box(Box0 _v) : v_(std::move(_v)) {}

    explicit box(Empty _v) : v_(_v) {}

    static box box0(std::function<uint64_t(uint64_t)> a0) {
      return box(Box0{std::move(a0)});
    }

    static box empty() { return box(Empty{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &,
                                   std::function<uint64_t(uint64_t)> &>
  static T1 box_rect(F0 &&f, T1 f0, const box &b) {
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[a0] = std::get<typename box::Box0>(b.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &,
                                   std::function<uint64_t(uint64_t)> &>
  static T1 box_rec(F0 &&f, T1 f0, const box &b) {
    if (std::holds_alternative<typename box::Box0>(b.v())) {
      const auto &[a0] = std::get<typename box::Box0>(b.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  /// A local fixpoint captures the function parameter n and is stored
  /// in Box — a user-defined inductive (not option, not pair).
  ///
  /// BUG: Local fixpoints generate std::function with & capture
  /// (needed for self-reference). This & also captures n by reference.
  /// The fixpoint escapes through Box, so return_captures_by_value
  /// does NOT apply. After make_box_fix returns, n is destroyed,
  /// and the captured reference dangles.
  ///
  /// Difference from fix_escape_capture: escapes through a CUSTOM
  /// INDUCTIVE constructor, not a pair.
  static box make_box_fix(uint64_t n);
  /// test1: make_box_fix(5) returns Box(add) where add(x) = x + 5.
  /// Expected: add(3) = 5 + 3 = 8.
  /// Bug: & captures dangling reference to n.
  static inline const uint64_t test1 = []() {
    auto &&_sv = make_box_fix(UINT64_C(5));
    if (std::holds_alternative<typename box::Box0>(_sv.v())) {
      const auto &[a0] = std::get<typename box::Box0>(_sv.v());
      return a0(UINT64_C(3));
    } else {
      return UINT64_C(999);
    }
  }();
  /// test2: Interleave noise between closure creation and use.
  /// Expected: add(10) = 42 + 10 = 52.
  static inline const uint64_t test2 = []() {
    box b = make_box_fix(UINT64_C(42));
    if (std::holds_alternative<typename box::Box0>(b.v_mut())) {
      auto &[a0] = std::get<typename box::Box0>(b.v_mut());
      return std::move(a0)(UINT64_C(10));
    } else {
      return UINT64_C(999);
    }
  }();
  /// test3: Two boxes — capture different parameters.
  /// Expected: add_10(0) + add_20(0) = 10 + 20 = 30.
  static inline const uint64_t test3 = []() {
    box b1 = make_box_fix(UINT64_C(10));
    box b2 = make_box_fix(UINT64_C(20));
    if (std::holds_alternative<typename box::Box0>(b1.v_mut())) {
      auto &[a0] = std::get<typename box::Box0>(b1.v_mut());
      if (std::holds_alternative<typename box::Box0>(b2.v_mut())) {
        auto &[a00] = std::get<typename box::Box0>(b2.v_mut());
        return (std::move(a0)(UINT64_C(0)) + std::move(a00)(UINT64_C(0)));
      } else {
        return UINT64_C(999);
      }
    } else {
      return UINT64_C(999);
    }
  }();
};

#endif // INCLUDED_CLOSURE_IN_CTOR
