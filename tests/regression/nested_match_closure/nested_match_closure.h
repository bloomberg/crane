#ifndef INCLUDED_NESTED_MATCH_CLOSURE
#define INCLUDED_NESTED_MATCH_CLOSURE

#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

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
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
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
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rec<T1>(f, f0, *a0), a1, *a2,
                tree_rec<T1>(f, f0, *a2));
    }
  }

  static uint64_t tree_sum(const tree &t);
  /// Pattern 1: Nested match creating a closure that captures from both levels.
  /// The fixpoint go captures outer_val from outer match and
  /// inner_val from inner match. Both are structured binding refs.
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  make_combiner(const tree &t);
  /// test1: Node (Node Leaf 10 Leaf) 20 Leaf
  /// outer_val = 20, l = Node Leaf 10 Leaf
  /// inner_val = 10, combined = 30
  /// go(5) = 30 + 5 = 35
  static constexpr uint64_t test1 = UINT64_C(35);
  /// Pattern 2: Triple nesting
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  make_deep_combiner(const tree &t);
  /// test2: Node (Node (Node Leaf 100 Leaf) 200 Leaf) 300 Leaf
  /// v1=300, v2=200, v3=100, total=600
  /// go(0) = 600
  static constexpr uint64_t test2 = UINT64_C(600);
  /// Pattern 3: Closure capturing variables from match AND function param.
  /// The fixpoint captures BOTH pattern variables AND the function parameter.
  /// After the function returns, BOTH the pattern variables AND the
  /// function parameter are dead.
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  make_param_combiner(const tree &t, uint64_t base);
  /// test3: Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf), base=1000
  /// go(0) = 1000 + 10 + 5 + 15 = 1030
  /// go(3) = 1030 + 3 = 1033
  static constexpr uint64_t test3 = UINT64_C(1033);
  /// Pattern 4: Store closure, THEN clobber stack with heavy computation
  static constexpr uint64_t test4 = UINT64_C(642);
};

#endif // INCLUDED_NESTED_MATCH_CLOSURE
