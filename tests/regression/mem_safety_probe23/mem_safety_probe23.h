#ifndef INCLUDED_MEM_SAFETY_PROBE23
#define INCLUDED_MEM_SAFETY_PROBE23

#include <memory>
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
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_shared<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_shared<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
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

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0,
                      const tree &t) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0_0;
      tree a2;
      uint64_t a1;
      tree a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      T1 _result;
      tree a2;
      uint64_t a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f.a2),
                                          _f.a1, std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            f0(_f.a0, std::move(_result), _f.a1, _f.a2, std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0,
                     const tree &t) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0_0;
      tree a2;
      uint64_t a1;
      tree a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      T1 _result;
      tree a2;
      uint64_t a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f.a2),
                                          _f.a1, std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            f0(_f.a0, std::move(_result), _f.a1, _f.a2, std::move(_f._result));
      }
    }
    return _result;
  }

  static uint64_t tree_sum(const tree &t);
  static uint64_t tree_size(const tree &t);
  /// TEST 1: Return the ORIGINAL tree alongside recursive child processing.
  /// t escapes because it is returned. Recursive calls on l and r (children).
  /// Loopifier must handle: owned param + pointer-safe children.
  static std::pair<tree, uint64_t> sum_with_original(tree t);
  static inline const uint64_t test_sum_with_original = []() {
    std::pair<tree, uint64_t> r = sum_with_original(tree::node(
        tree::node(tree::leaf(), UINT64_C(3), tree::leaf()), UINT64_C(7),
        tree::node(tree::leaf(), UINT64_C(11), tree::leaf())));
    return (r.second + tree_sum(r.first));
  }();
  /// TEST 2: Return a PAIR of the original tree and a transformed copy.
  /// Forces tree to be owned; two recursive calls on children.
  static std::pair<tree, tree> dup_and_double(tree t);
  static inline const uint64_t test_dup_and_double = []() {
    std::pair<tree, tree> r = dup_and_double(tree::node(
        tree::node(tree::leaf(), UINT64_C(3), tree::leaf()), UINT64_C(5),
        tree::node(tree::leaf(), UINT64_C(7), tree::leaf())));
    return (tree_sum(r.first) + tree_sum(r.second));
  }();
  /// TEST 3: Store children in result alongside recursive processing.
  /// l and r are extracted from match, BOTH used in result AND in
  /// recursive calls. Tests whether children are correctly cloned when
  /// they appear in both continuation and recursive positions.
  static std::pair<std::pair<tree, tree>, uint64_t>
  collect_children(const tree &t);
  static inline const uint64_t test_collect_children = []() {
    std::pair<std::pair<tree, tree>, uint64_t> r = collect_children(tree::node(
        tree::node(tree::leaf(), UINT64_C(2), tree::leaf()), UINT64_C(5),
        tree::node(tree::leaf(), UINT64_C(8), tree::leaf())));
    const std::pair<tree, tree> &p = r.first;
    const uint64_t &s = r.second;
    const tree &left_child = p.first;
    const tree &right_child = p.second;
    return ((tree_sum(left_child) + tree_sum(right_child)) + s);
  }();
  /// TEST 4: Recursive function that rebuilds tree with an
  /// ACCUMULATOR that captures the original tree. The accumulator
  /// forces the tree to be owned. Two recursive calls on children.
  static std::pair<tree, uint64_t> sum_with_acc(const tree &t, uint64_t acc);
  static inline const uint64_t test_sum_with_acc = []() {
    std::pair<tree, uint64_t> r = sum_with_acc(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        UINT64_C(0));
    return (r.second + tree_sum(r.first));
  }();
  /// TEST 5: Function using tree_sum on children INSIDE the same
  /// expression as recursive calls. Tests that child pointers remain
  /// valid when other operations happen on the same tree.
  static std::pair<uint64_t, uint64_t> interleaved_ops(const tree &t);
  static inline const uint64_t test_interleaved_ops = []() {
    std::pair<uint64_t, uint64_t> r = interleaved_ops(tree::node(
        tree::node(tree::leaf(), UINT64_C(2), tree::leaf()), UINT64_C(5),
        tree::node(tree::leaf(), UINT64_C(3), tree::leaf())));
    return (r.first + r.second);
  }();
  /// TEST 6: Nested tree type — tree of trees. Tests clone correctness
  /// for deeply nested value types.
  static uint64_t flatten_tree_of_trees(const tree &t, tree inner);
  static inline const uint64_t test_flatten_tree_of_trees =
      flatten_tree_of_trees(
          tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                     UINT64_C(2),
                     tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()));
  /// TEST 7: Two recursive calls where one takes a CONSTRUCTED tree
  /// with t embedded AND another takes a child of t.
  /// Forces t to NOT be pointer-safe. The After frame saves
  /// state for the child-based call.
  static uint64_t mixed_recurse(tree t, uint64_t n);
  static inline const uint64_t test_mixed_recurse = mixed_recurse(
      tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(1));
  /// TEST 8: Three-way split: function returns original tree AND
  /// uses tree_size on children. Forces tree owned; exercises
  /// the interplay between clone, move, and raw pointer in
  /// continuation frames.
  static std::pair<tree, uint64_t> annotate_sizes(const tree &t);
  static inline const uint64_t test_annotate_sizes = []() {
    std::pair<tree, uint64_t> r = annotate_sizes(tree::node(
        tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(20),
        tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
    return (tree_sum(r.first) + r.second);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE23
