#ifndef INCLUDED_NESTED_PARTIAL_APP
#define INCLUDED_NESTED_PARTIAL_APP

#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct NestedPartialApp {
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
  /// 3-argument function: builds Node(t1, n, t2).
  static tree build_node(const tree &t1, uint64_t n, const tree &t2);
  /// BUG HYPOTHESIS: Partially apply build_node in stages.
  /// g = build_node t1  → closure captures t1
  /// h = g 42           → closure captures t1 and 42
  /// Then invoke h twice with different args.
  /// If captures are moved, second invocation fails.
  ///
  /// Expected:
  /// t1 = Node Leaf 10 Leaf (sum = 10)
  /// h c1 = Node(t1, 42, c1)
  /// h c2 = Node(t1, 42, c2)
  /// tree_sum(h c1) + tree_sum(h c2) where c1=Node Leaf 1 Leaf, c2=Node Leaf 2
  /// Leaf = (10 + 42 + 1) + (10 + 42 + 2) = 53 + 54 = 107
  static constexpr uint64_t nested_partial_bug = UINT64_C(107);
  /// Variation: use intermediate partial app g twice before further
  /// partial application. Tests if g's capture of t1 survives.
  static constexpr uint64_t nested_partial_reuse = UINT64_C(164);
  /// Variation: 4-argument function, triple nesting.
  static uint64_t quad_fn(const tree &a, uint64_t b, uint64_t c, const tree &d);
  static constexpr uint64_t triple_partial = UINT64_C(123);
};

#endif // INCLUDED_NESTED_PARTIAL_APP
