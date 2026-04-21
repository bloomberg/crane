#ifndef INCLUDED_FIX_FOLD_ESCAPE
#define INCLUDED_FIX_FOLD_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct FixFoldEscape {
  /// Manual fold_left to avoid stdlib extraction complications.
  template <
      MapsTo<std::shared_ptr<List<std::function<unsigned int(unsigned int)>>>,
             std::shared_ptr<List<std::function<unsigned int(unsigned int)>>>,
             unsigned int>
          F0>
  static std::shared_ptr<List<std::function<unsigned int(unsigned int)>>>
  fold_left(
      F0 &&f,
      std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> acc,
      const std::shared_ptr<List<unsigned int>> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
      return acc;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l->v());
      return fold_left(f, f(std::move(acc), d_a0), d_a1);
    }
  }

  /// Collect fixpoint closures by folding over a list of nats.
  /// Each iteration creates a new fixpoint adder that captures the
  /// current element n from the fold callback's parameter.
  ///
  /// BUG HYPOTHESIS: The callback lambda's parameter n lives on the
  /// callback's stack frame. The fixpoint adder captures n by &.
  /// The callback returns cons adder acc, storing the closure.
  /// After the callback returns, n is destroyed. Later iterations and
  /// the final result contain dangling closures.
  static std::shared_ptr<List<std::function<unsigned int(unsigned int)>>>
  collect_adders(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int apply_head(
      const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> &l,
      const unsigned int x);
  __attribute__((pure)) static unsigned int sum_apply(
      const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> &l,
      const unsigned int x); /// test1: collect_adders 10; 20; 30 -> adder_30;
                             /// adder_20; adder_10
  /// (reversed by fold_left). apply_head picks adder_30, apply to 5 -> 35.
  static inline const unsigned int test1 = apply_head(
      collect_adders(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil())))),
      5u);
  /// test2: Sum all adders applied to 0.
  /// adder_30(0) + adder_20(0) + adder_10(0) = 30 + 20 + 10 = 60.
  static inline const unsigned int test2 = sum_apply(
      collect_adders(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil())))),
      0u);
  /// test3: With noise between collection and use.
  static inline const unsigned int test3 = []() {
    std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> fns =
        collect_adders(List<unsigned int>::cons(
            100u, List<unsigned int>::cons(200u, List<unsigned int>::nil())));
    unsigned int noise = ((55u + 44u) + 33u);
    return (apply_head(std::move(fns), 0u) + noise);
  }();
};

#endif // INCLUDED_FIX_FOLD_ESCAPE
