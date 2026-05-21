#ifndef INCLUDED_REUSE_MOVE_SHADOW
#define INCLUDED_REUSE_MOVE_SHADOW

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ReuseMoveShadow {
  /// Define node FIRST so it gets variant index 0 and the reuse
  /// optimization picks the node branch via List.hd reuse_candidates.
  struct tree {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<tree> a1;
      std::shared_ptr<tree> a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    explicit tree(Leaf _v) : v_(_v) {}

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Node>(_src->v())) {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0, _alt.a1 ? std::make_shared<tree>() : nullptr,
                          _alt.a2 ? std::make_shared<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        } else {
          _dst->v_ = Leaf{};
        }
      }
      return _out;
    }

    // CREATORS
    static tree node(uint64_t a0, tree a1, tree a2) {
      return tree(Node{a0, std::make_shared<tree>(std::move(a1)),
                       std::make_shared<tree>(std::move(a2))});
    }

    static tree leaf() { return tree(Leaf{}); }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, tree &, T1 &, tree &,
                                   T1 &>
  static T1 tree_rect(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rect<T1>(f, f0, *a1), *a2,
               tree_rect<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, tree &, T1 &, tree &,
                                   T1 &>
  static T1 tree_rec(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rec<T1>(f, f0, *a1), *a2,
               tree_rec<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  static uint64_t tree_sum(const tree &t);
  /// BUG: The reuse branch does not shift move_dead_after or
  /// move_owned_vars when pushing pattern variables.
  ///
  /// In dup_left, the parameter t is at de Bruijn index 2, and is owned
  /// (escapes in the else branch).  After pushing 3 pattern variables
  /// (v at 1, l at 2, r at 3), the pattern variable l lands at index 2 —
  /// colliding with the un-shifted index for t in move_dead_after and
  /// move_owned_vars.
  ///
  /// The non-reuse path correctly calls with_shifted_move_tracking which
  /// shifts both sets by n_pat_vars and clears move_dead_after.  But the
  /// reuse path (lines ~4537-4602 in translation.ml) calls
  /// process_match_pattern_vars WITHOUT shifting.
  ///
  /// Since l appears TWICE in the body (node v l l), the assign loop
  /// generates gen_expr body_env (MLrel 2) for each.  Both checks hit
  /// move_dead_after and move_owned_vars at index 2 (thinking it refers to
  /// the dead/owned t), so both emit std::move(l):
  ///
  /// _rf.d_a1 = std::move(l);   // l moved, now null
  /// _rf.d_a2 = std::move(l);   // l is null!  assigns null
  ///
  /// The returned tree has d_a2 = nullptr.  Traversing the right subtree
  /// crashes with a null-pointer dereference.
  static tree dup_left(tree t, bool b);
  /// test1: dup_left (node 10 (node 1 leaf leaf) (node 2 leaf leaf)) true
  /// Expected result: node 10 (node 1 leaf leaf) (node 1 leaf leaf)
  /// tree_sum = 10 + 1 + 0 + 0 + 1 + 0 + 0 = 12
  /// BUG: right subtree is null -> crash in tree_sum.
  static inline const uint64_t test1 = tree_sum(
      dup_left(tree::node(UINT64_C(10),
                          tree::node(UINT64_C(1), tree::leaf(), tree::leaf()),
                          tree::node(UINT64_C(2), tree::leaf(), tree::leaf())),
               true));
  /// test2: Deeper tree to stress memory.
  /// dup_left (node 5 (node 3 (node 4 leaf leaf) leaf) leaf) true
  /// Expected: node 5 (node 3 (node 4 leaf leaf) leaf) (node 3 (node 4 leaf
  /// leaf) leaf) tree_sum = 5 + (3 + 4 + 0) + (3 + 4 + 0) = 19 BUG: right
  /// subtree is null -> crash.
  static inline const uint64_t test2 = tree_sum(dup_left(
      tree::node(UINT64_C(5),
                 tree::node(UINT64_C(3),
                            tree::node(UINT64_C(4), tree::leaf(), tree::leaf()),
                            tree::leaf()),
                 tree::leaf()),
      true));
  /// test3: Non-reuse path (use_count > 1).
  /// This should work correctly because the normal branch uses
  /// with_shifted_move_tracking which properly shifts the indices.
  static inline const uint64_t test3 = []() {
    tree t = tree::node(UINT64_C(7),
                        tree::node(UINT64_C(8), tree::leaf(), tree::leaf()),
                        tree::node(UINT64_C(9), tree::leaf(), tree::leaf()));
    return (tree_sum(dup_left(t, true)) + tree_sum(t));
  }();
};

#endif // INCLUDED_REUSE_MOVE_SHADOW
