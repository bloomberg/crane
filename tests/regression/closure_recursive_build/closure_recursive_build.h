#ifndef INCLUDED_CLOSURE_RECURSIVE_BUILD
#define INCLUDED_CLOSURE_RECURSIVE_BUILD

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ClosureRecursiveBuild {
  /// A list of closures, each one of which captures a different value.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<uint64_t(uint64_t)> a0;
      std::shared_ptr<fn_list> a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    fn_list() {}

    explicit fn_list(FNil _v) : v_(_v) {}

    explicit fn_list(FCons _v) : v_(std::move(_v)) {}

    static fn_list fnil() { return fn_list(FNil{}); }

    static fn_list fcons(std::function<uint64_t(uint64_t)> a0, fn_list a1) {
      return fn_list(
          FCons{std::move(a0), std::make_shared<fn_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~fn_list() {
      std::vector<std::shared_ptr<fn_list>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<FCons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<
        T1, F1 &, std::function<uint64_t(uint64_t)> &, fn_list &, T1 &>
  static T1 fn_list_rect(T1 f, F1 &&f0, const fn_list &f1) {
    if (std::holds_alternative<typename fn_list::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename fn_list::FCons>(f1.v());
      return f0(a0, *a1, fn_list_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<
        T1, F1 &, std::function<uint64_t(uint64_t)> &, fn_list &, T1 &>
  static T1 fn_list_rec(T1 f, F1 &&f0, const fn_list &f1) {
    if (std::holds_alternative<typename fn_list::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename fn_list::FCons>(f1.v());
      return f0(a0, *a1, fn_list_rec<T1>(f, f0, *a1));
    }
  }

  /// Recursively build a list of fixpoint closures. Each recursive call
  /// creates a local fixpoint adder that captures the current n.
  ///
  /// BUG HYPOTHESIS: Each adder captures n from its stack frame
  /// by &. The closures are stored in FCons constructors. After
  /// build_adders returns, all intermediate stack frames are gone,
  /// and every closure holds a dangling reference.
  static fn_list build_adders(uint64_t n);
  static uint64_t apply_first(const fn_list &fl, uint64_t x);
  static uint64_t apply_all_sum(const fn_list &fl, uint64_t x);
  /// test1: build_adders(3) = adder_3, adder_2, adder_1.
  /// apply_first returns adder_3(10) = 3 + 10 = 13.
  static inline const uint64_t test1 =
      apply_first(build_adders(UINT64_C(3)), UINT64_C(10));
  /// test2: apply_all_sum sums all adders applied to 0.
  /// adder_3(0) + adder_2(0) + adder_1(0) = 3 + 2 + 1 = 6.
  static inline const uint64_t test2 =
      apply_all_sum(build_adders(UINT64_C(3)), UINT64_C(0));
  /// test3: with noise between build and use.
  /// build_adders(5), noise, then apply_first(fns, 0) = 5.
  static inline const uint64_t test3 = []() {
    fn_list fns = build_adders(UINT64_C(5));
    uint64_t noise = ((UINT64_C(99) + UINT64_C(88)) + UINT64_C(77));
    return (apply_first(std::move(fns), UINT64_C(0)) + noise);
  }();
};

#endif // INCLUDED_CLOSURE_RECURSIVE_BUILD
