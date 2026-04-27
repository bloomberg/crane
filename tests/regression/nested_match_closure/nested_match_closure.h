#ifndef INCLUDED_NESTED_MATCH_CLOSURE
#define INCLUDED_NESTED_MATCH_CLOSURE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NestedMatchClosure {
  /// NESTED MATCH WITH CLOSURES
  ///
  /// BUG HYPOTHESIS: When two levels of pattern matching create
  /// structured bindings, and a closure in the inner match captures
  /// variables from BOTH levels, the outer bindings might be invalid
  /// by the time the closure is invoked.
  ///
  /// This is different from existing wip tests because:
  /// 1. The captured variables come from MULTIPLE nesting levels
  /// 2. The structured bindings from outer match may reference
  /// different shared_ptr nodes
  /// 3. The inner match might consume/move its scrutinee, invalidating
  /// outer bindings that reference the same shared_ptr
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(Node{
            d_a0 ? std::make_unique<NestedMatchClosure::tree>(d_a0->clone())
                 : nullptr,
            d_a1,
            d_a2 ? std::make_unique<NestedMatchClosure::tree>(d_a2->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(const tree &a0, unsigned int a1,
                                           const tree &a2) {
      return tree(Node{std::make_unique<tree>(a0), std::move(a1),
                       std::make_unique<tree>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree *operator->() { return this; }

    __attribute__((pure)) const tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  __attribute__((pure)) static unsigned int tree_sum(const tree &t);
  /// Pattern 1: Nested match creating a closure that captures from both levels.
  /// The fixpoint go captures outer_val from outer match and
  /// inner_val from inner match. Both are structured binding refs.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_combiner(const tree &t);
  /// test1: Node (Node Leaf 10 Leaf) 20 Leaf
  /// outer_val = 20, l = Node Leaf 10 Leaf
  /// inner_val = 10, combined = 30
  /// go(5) = 30 + 5 = 35
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_combiner(tree::node(
        tree::node(tree::leaf(), 10u, tree::leaf()), 20u, tree::leaf()));
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(5u);
    } else {
      return 999u;
    }
  }();
  /// Pattern 2: Triple nesting
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_deep_combiner(const tree &t);
  /// test2: Node (Node (Node Leaf 100 Leaf) 200 Leaf) 300 Leaf
  /// v1=300, v2=200, v3=100, total=600
  /// go(0) = 600
  static inline const unsigned int test2 = []() -> unsigned int {
    auto _cs = make_deep_combiner(
        tree::node(tree::node(tree::node(tree::leaf(), 100u, tree::leaf()),
                              200u, tree::leaf()),
                   300u, tree::leaf()));
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(0u);
    } else {
      return 999u;
    }
  }();
  /// Pattern 3: Closure capturing variables from match AND function param.
  /// The fixpoint captures BOTH pattern variables AND the function parameter.
  /// After the function returns, BOTH the pattern variables AND the
  /// function parameter are dead.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_param_combiner(const tree &t, unsigned int base);
  /// test3: Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf), base=1000
  /// go(0) = 1000 + 10 + 5 + 15 = 1030
  /// go(3) = 1030 + 3 = 1033
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_param_combiner(
        tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                   tree::node(tree::leaf(), 15u, tree::leaf())),
        1000u);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(3u);
    } else {
      return 999u;
    }
  }();
  /// Pattern 4: Store closure, THEN clobber stack with heavy computation
  static inline const unsigned int test4 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> f =
        make_param_combiner(
            tree::node(tree::node(tree::leaf(), 42u, tree::leaf()), 100u,
                       tree::leaf()),
            500u);
    if (f.has_value()) {
      const std::function<unsigned int(unsigned int)> &g = *f;
      return g(0u);
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_NESTED_MATCH_CLOSURE
