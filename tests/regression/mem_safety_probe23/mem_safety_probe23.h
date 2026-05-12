#ifndef INCLUDED_MEM_SAFETY_PROBE23
#define INCLUDED_MEM_SAFETY_PROBE23

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe23 {
  /// Probe 23: Owned-parameter loopification with child recursion.
  ///
  /// Attack vector: Make the tree parameter OWNED (by value) by having
  /// the function return or store the original tree, while ALSO recursing
  /// on the tree's children. If the loopifier stores the tree by value in
  /// Enter frames AND stores raw pointers to children in After frames
  /// (because children flow to pointer-safe positions), the raw pointers
  /// dangle when the Enter frame's tree goes out of scope.
  ///
  /// Secondary: test interactions between loop variable reuse, clone
  /// correctness, and move semantics for complex value types.
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

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
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
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->d_v_ = Leaf();
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node(_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr);
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf()); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node(std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))));
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                   tree &, T1 &>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                   tree &, T1 &>
  static T1 tree_rec(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  static unsigned int tree_sum(const tree &t);
  static unsigned int tree_size(const tree &t);
  /// TEST 1: Return the ORIGINAL tree alongside recursive child processing.
  /// t escapes because it is returned. Recursive calls on l and r (children).
  /// Loopifier must handle: owned param + pointer-safe children.
  static std::pair<tree, unsigned int> sum_with_original(tree t);
  static inline const unsigned int test_sum_with_original = []() {
    std::pair<tree, unsigned int> r = sum_with_original(
        tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                   tree::node(tree::leaf(), 11u, tree::leaf())));
    return (r.second + tree_sum(r.first));
  }();
  /// TEST 2: Return a PAIR of the original tree and a transformed copy.
  /// Forces tree to be owned; two recursive calls on children.
  static std::pair<tree, tree> dup_and_double(tree t);
  static inline const unsigned int test_dup_and_double = []() {
    std::pair<tree, tree> r = dup_and_double(
        tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 5u,
                   tree::node(tree::leaf(), 7u, tree::leaf())));
    return (tree_sum(r.first) + tree_sum(r.second));
  }();
  /// TEST 3: Store children in result alongside recursive processing.
  /// l and r are extracted from match, BOTH used in result AND in
  /// recursive calls. Tests whether children are correctly cloned when
  /// they appear in both continuation and recursive positions.
  static std::pair<std::pair<tree, tree>, unsigned int>
  collect_children(const tree &t);
  static inline const unsigned int test_collect_children = []() {
    std::pair<std::pair<tree, tree>, unsigned int> r = collect_children(
        tree::node(tree::node(tree::leaf(), 2u, tree::leaf()), 5u,
                   tree::node(tree::leaf(), 8u, tree::leaf())));
    const std::pair<tree, tree> &p = r.first;
    const unsigned int &s = r.second;
    const tree &left_child = p.first;
    const tree &right_child = p.second;
    return ((tree_sum(left_child) + tree_sum(right_child)) + s);
  }();
  /// TEST 4: Recursive function that rebuilds tree with an
  /// ACCUMULATOR that captures the original tree. The accumulator
  /// forces the tree to be owned. Two recursive calls on children.
  static std::pair<tree, unsigned int> sum_with_acc(const tree &t,
                                                    const unsigned int acc);
  static inline const unsigned int test_sum_with_acc = []() {
    std::pair<tree, unsigned int> r =
        sum_with_acc(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                                tree::node(tree::leaf(), 3u, tree::leaf())),
                     0u);
    return (r.second + tree_sum(r.first));
  }();
  /// TEST 5: Function using tree_sum on children INSIDE the same
  /// expression as recursive calls. Tests that child pointers remain
  /// valid when other operations happen on the same tree.
  static std::pair<unsigned int, unsigned int> interleaved_ops(const tree &t);
  static inline const unsigned int test_interleaved_ops = []() {
    std::pair<unsigned int, unsigned int> r = interleaved_ops(
        tree::node(tree::node(tree::leaf(), 2u, tree::leaf()), 5u,
                   tree::node(tree::leaf(), 3u, tree::leaf())));
    return (r.first + r.second);
  }();
  /// TEST 6: Nested tree type — tree of trees. Tests clone correctness
  /// for deeply nested value types.
  static unsigned int flatten_tree_of_trees(const tree &t, tree inner);
  static inline const unsigned int test_flatten_tree_of_trees =
      flatten_tree_of_trees(
          tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                     tree::node(tree::leaf(), 3u, tree::leaf())),
          tree::node(tree::leaf(), 10u, tree::leaf()));
  /// TEST 7: Two recursive calls where one takes a CONSTRUCTED tree
  /// with t embedded AND another takes a child of t.
  /// Forces t to NOT be pointer-safe. The After frame saves
  /// state for the child-based call.
  static unsigned int mixed_recurse(tree t, const unsigned int n);
  static inline const unsigned int test_mixed_recurse =
      mixed_recurse(tree::node(tree::leaf(), 5u, tree::leaf()), 1u);
  /// TEST 8: Three-way split: function returns original tree AND
  /// uses tree_size on children. Forces tree owned; exercises
  /// the interplay between clone, move, and raw pointer in
  /// continuation frames.
  static std::pair<tree, unsigned int> annotate_sizes(const tree &t);
  static inline const unsigned int test_annotate_sizes = []() {
    std::pair<tree, unsigned int> r = annotate_sizes(
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf())));
    return (tree_sum(r.first) + r.second);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE23
