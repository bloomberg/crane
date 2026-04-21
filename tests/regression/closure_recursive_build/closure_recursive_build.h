#ifndef INCLUDED_CLOSURE_RECURSIVE_BUILD
#define INCLUDED_CLOSURE_RECURSIVE_BUILD

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ClosureRecursiveBuild {
  /// A list of closures, each one of which captures a different value.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<unsigned int(unsigned int)> d_a0;
      std::shared_ptr<fn_list> d_a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit fn_list(FNil _v) : d_v_(_v) {}

    explicit fn_list(FCons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<fn_list> fnil() {
      return std::make_shared<fn_list>(FNil{});
    }

    static std::shared_ptr<fn_list>
    fcons(std::function<unsigned int(unsigned int)> a0,
          const std::shared_ptr<fn_list> &a1) {
      return std::make_shared<fn_list>(FCons{std::move(a0), a1});
    }

    static std::shared_ptr<fn_list>
    fcons(std::function<unsigned int(unsigned int)> a0,
          std::shared_ptr<fn_list> &&a1) {
      return std::make_shared<fn_list>(FCons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::function<unsigned int(unsigned int)>,
                                std::shared_ptr<fn_list>, T1>
                             F1>
  static T1 fn_list_rect(const T1 f, F1 &&f0,
                         const std::shared_ptr<fn_list> &f1) {
    if (std::holds_alternative<typename fn_list::FNil>(f1->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(f1->v());
      return f0(d_a0, d_a1, fn_list_rect<T1>(f, f0, d_a1));
    }
  }

  template <typename T1, MapsTo<T1, std::function<unsigned int(unsigned int)>,
                                std::shared_ptr<fn_list>, T1>
                             F1>
  static T1 fn_list_rec(const T1 f, F1 &&f0,
                        const std::shared_ptr<fn_list> &f1) {
    if (std::holds_alternative<typename fn_list::FNil>(f1->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename fn_list::FCons>(f1->v());
      return f0(d_a0, d_a1, fn_list_rec<T1>(f, f0, d_a1));
    }
  }

  /// Recursively build a list of fixpoint closures. Each recursive call
  /// creates a local fixpoint adder that captures the current n.
  ///
  /// BUG HYPOTHESIS: Each adder captures n from its stack frame
  /// by &. The closures are stored in FCons constructors. After
  /// build_adders returns, all intermediate stack frames are gone,
  /// and every closure holds a dangling reference.
  static std::shared_ptr<fn_list> build_adders(const unsigned int n);
  __attribute__((pure)) static unsigned int
  apply_first(const std::shared_ptr<fn_list> &fl, const unsigned int x);
  __attribute__((pure)) static unsigned int
  apply_all_sum(const std::shared_ptr<fn_list> &fl, const unsigned int x);
  /// test1: build_adders(3) = adder_3, adder_2, adder_1.
  /// apply_first returns adder_3(10) = 3 + 10 = 13.
  static inline const unsigned int test1 = apply_first(build_adders(3u), 10u);
  /// test2: apply_all_sum sums all adders applied to 0.
  /// adder_3(0) + adder_2(0) + adder_1(0) = 3 + 2 + 1 = 6.
  static inline const unsigned int test2 = apply_all_sum(build_adders(3u), 0u);
  /// test3: with noise between build and use.
  /// build_adders(5), noise, then apply_first(fns, 0) = 5.
  static inline const unsigned int test3 = []() {
    std::shared_ptr<fn_list> fns = build_adders(5u);
    unsigned int noise = ((99u + 88u) + 77u);
    return (apply_first(std::move(fns), 0u) + noise);
  }();
};

#endif // INCLUDED_CLOSURE_RECURSIVE_BUILD
