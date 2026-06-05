#ifndef INCLUDED_REUSE_SCRUTINEE
#define INCLUDED_REUSE_SCRUTINEE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ReuseScrutinee {
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

  /// Extract the value from the left subtree.
  /// This accesses the Node's d_a0 field (left subtree).
  static uint64_t left_val(const tree &t);
  /// Extract the value from the right subtree.
  static uint64_t right_val(const tree &t);
  /// Sum of left and right subtree values.
  static uint64_t subtree_sum(const tree &t);
  /// REUSE BUG TRIGGER:
  /// The match on t returns Node Leaf (subtree_sum t) Leaf.
  /// If the reuse optimization fires (t.use_count() == 1):
  /// 1. Fields are moved out: l = move(d_a0), r = move(d_a2)
  /// → d_a0 and d_a2 are now null
  /// 2. New values are computed: subtree_sum(t) accesses t's subtrees
  /// → t's d_a0 is null → left_val dereferences null → CRASH
  static inline const uint64_t reuse_bug = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    if (std::holds_alternative<typename tree::Leaf>(t.v_mut())) {
      return UINT64_C(0);
    } else {
      return subtree_sum(t);
    }
  }();
  /// Direct version: the result directly uses the scrutinee in a
  /// tail constructor that could trigger reuse.
  static inline const tree reuse_direct = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    if (std::holds_alternative<typename tree::Leaf>(t.v_mut())) {
      return tree::leaf();
    } else {
      auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v_mut());
      return tree::node(tree::leaf(), subtree_sum(t), *a2);
    }
  }();
  /// Expected: subtree_sum on Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf))
  /// = left_val + right_val = 10 + 30 = 40
  static inline const uint64_t expected_sum = subtree_sum(tree::node(
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(20),
      tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
};

#endif // INCLUDED_REUSE_SCRUTINEE
