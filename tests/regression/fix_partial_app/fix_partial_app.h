#ifndef INCLUDED_FIX_PARTIAL_APP
#define INCLUDED_FIX_PARTIAL_APP

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct FixPartialApp {
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
      std::vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
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

  /// count_nodes: counts nodes in a tree. Will be partially applied.
  static uint64_t count_nodes(const tree &t, uint64_t base);
  /// BUG HYPOTHESIS: Partially applying a fixpoint.
  /// f := count_nodes big_tree creates a closure (nat -> nat).
  /// The closure captures the fixpoint AND the tree.
  /// If either is captured by &, it's a dangling reference.
  ///
  /// big_tree = Node(Node(Leaf,0,Leaf), 0, Node(Leaf,0,Leaf))
  /// count_nodes big_tree 0 = count_nodes left (count_nodes right (0+1))
  /// = count_nodes left (count_nodes right 1)
  /// = count_nodes Leaf (count_nodes Leaf (1+1))
  /// = count_nodes Leaf (count_nodes Leaf 2)
  /// = count_nodes Leaf 2 = 2
  /// Wait that's wrong. Let me recalculate:
  /// count_nodes (Node l v r) base = count_nodes l (count_nodes r (base + 1))
  ///
  /// tree = Node(Node(Leaf,0,Leaf), 0, Node(Leaf,0,Leaf))
  /// count_nodes tree 0
  /// = count_nodes (Node(Leaf,0,Leaf)) (count_nodes (Node(Leaf,0,Leaf)) (0+1))
  /// = count_nodes (Node(Leaf,0,Leaf)) (count_nodes (Node(Leaf,0,Leaf)) 1)
  ///
  /// count_nodes (Node(Leaf,0,Leaf)) 1
  /// = count_nodes Leaf (count_nodes Leaf (1+1))
  /// = count_nodes Leaf (count_nodes Leaf 2)
  /// = count_nodes Leaf 2
  /// = 2
  ///
  /// count_nodes (Node(Leaf,0,Leaf)) 2
  /// = count_nodes Leaf (count_nodes Leaf (2+1))
  /// = count_nodes Leaf 3
  /// = 3
  ///
  /// So count_nodes tree 0 = 3
  static inline const uint64_t fix_partial_bug = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(0), tree::leaf()),
                          UINT64_C(0),
                          tree::node(tree::leaf(), UINT64_C(0), tree::leaf()));
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t { return count_nodes(t, _x0); };
      return (f(UINT64_C(0)) + f(UINT64_C(100)));
    }();
  }();
  /// Same but store partial app in pair
  static inline const uint64_t fix_partial_pair = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(0), tree::leaf()),
                          UINT64_C(0),
                          tree::node(tree::leaf(), UINT64_C(0), tree::leaf()));
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t { return count_nodes(t, _x0); };
      std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
          std::make_pair(f, UINT64_C(42));
      return (p.first(UINT64_C(0)) + p.first(UINT64_C(100)));
    }();
  }();

  /// More complex: partial app of tree_map, a structure-preserving function.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static tree tree_map(F0 &&f, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return tree::leaf();
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return tree::node(tree_map(f, *a0), f(a1), tree_map(f, *a2));
    }
  }

  static uint64_t tree_sum(const tree &t);
  /// Partial app of tree_map: g := tree_map (fun x => x + 1)
  /// Then apply g to two different trees.
  /// If the closure for g captures the function arg by &, it could dangle.
  static inline const uint64_t map_partial_bug = []() {
    std::function<tree(tree)> g = [](tree _x0) -> tree {
      return tree_map([](uint64_t x) { return (x + UINT64_C(1)); }, _x0);
    };
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    return (tree_sum(g(std::move(t1))) + tree_sum(g(std::move(t2))));
  }();
};

#endif // INCLUDED_FIX_PARTIAL_APP
