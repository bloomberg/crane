#ifndef INCLUDED_HOF_CLOSURE_ESCAPE
#define INCLUDED_HOF_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct HofClosureEscape {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, *a2,
                tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rec<T1>(f, f0, *a0), a1, *a2,
                tree_rec<T1>(f, f0, *a2));
    }
  }

  static uint64_t sum_values(const tree &t, uint64_t x);

  /// wrap_some is a helper that takes a function and wraps it in Some.
  /// The partial application happens at the CALL SITE of wrap_some,
  /// so the & lambda is created by the caller and passed through.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static std::optional<std::function<uint64_t(uint64_t)>> wrap_some(F0 &&f) {
    return std::make_optional<std::function<uint64_t(uint64_t)>>(f);
  }

  /// BUG: The partial application sum_values t creates a & lambda.
  /// Even though wrap_some just passes f through to Some,
  /// the & lambda was created in hof_escape's stack frame.
  /// When hof_escape returns, captured t is destroyed.
  static std::optional<std::function<uint64_t(uint64_t)>>
  hof_escape(const tree &t);
  static uint64_t
  apply_option(const std::optional<std::function<uint64_t(uint64_t)>> &o,
               uint64_t x); /// Clobber stack, then use the closure.
  static inline const uint64_t bug_hof_escape = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                         UINT64_C(20),
                         tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::optional<std::function<uint64_t(uint64_t)>> o1 =
        hof_escape(std::move(t1));
    return apply_option(o1, UINT64_C(0));
  }();
};

#endif // INCLUDED_HOF_CLOSURE_ESCAPE
