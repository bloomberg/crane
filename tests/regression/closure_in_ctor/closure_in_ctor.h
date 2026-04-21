#ifndef INCLUDED_CLOSURE_IN_CTOR
#define INCLUDED_CLOSURE_IN_CTOR

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ClosureInCtor {
  struct box {
    // TYPES
    struct Box0 {
      std::function<unsigned int(unsigned int)> d_a0;
    };

    struct Empty {};

    using variant_t = std::variant<Box0, Empty>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit box(Box0 _v) : d_v_(std::move(_v)) {}

    explicit box(Empty _v) : d_v_(_v) {}

    static std::shared_ptr<box>
    box0(std::function<unsigned int(unsigned int)> a0) {
      return std::make_shared<box>(Box0{std::move(a0)});
    }

    static std::shared_ptr<box> empty() {
      return std::make_shared<box>(Empty{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
  static T1 box_rect(F0 &&f, const T1 f0, const std::shared_ptr<box> &b) {
    if (std::holds_alternative<typename box::Box0>(b->v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b->v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1,
            MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
  static T1 box_rec(F0 &&f, const T1 f0, const std::shared_ptr<box> &b) {
    if (std::holds_alternative<typename box::Box0>(b->v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b->v());
      return f(d_a0);
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
  static std::shared_ptr<box> make_box_fix(const unsigned int n);
  /// test1: make_box_fix(5) returns Box(add) where add(x) = x + 5.
  /// Expected: add(3) = 5 + 3 = 8.
  /// Bug: & captures dangling reference to n.
  static inline const unsigned int test1 = []() {
    auto &&_sv = make_box_fix(5u);
    if (std::holds_alternative<typename box::Box0>(_sv->v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(_sv->v());
      return d_a0(3u);
    } else {
      return 999u;
    }
  }();
  /// test2: Interleave noise between closure creation and use.
  /// Expected: add(10) = 42 + 10 = 52.
  static inline const unsigned int test2 = []() {
    std::shared_ptr<box> b = make_box_fix(42u);
    if (std::holds_alternative<typename box::Box0>(b->v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b->v());
      return d_a0(10u);
    } else {
      return 999u;
    }
  }();
  /// test3: Two boxes — capture different parameters.
  /// Expected: add_10(0) + add_20(0) = 10 + 20 = 30.
  static inline const unsigned int test3 = []() {
    std::shared_ptr<box> b1 = make_box_fix(10u);
    std::shared_ptr<box> b2 = make_box_fix(20u);
    if (std::holds_alternative<typename box::Box0>(b1->v())) {
      const auto &[d_a0] = std::get<typename box::Box0>(b1->v());
      if (std::holds_alternative<typename box::Box0>(b2->v())) {
        const auto &[d_a00] = std::get<typename box::Box0>(b2->v());
        return (d_a0(0u) + d_a00(0u));
      } else {
        return 999u;
      }
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_CLOSURE_IN_CTOR
