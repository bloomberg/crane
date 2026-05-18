#ifndef INCLUDED_MEM_SAFETY_PROBE8
#define INCLUDED_MEM_SAFETY_PROBE8

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe8 {
  /// These tests probe the interaction between:
  /// 1. OWNED tree parameters in loopified functions
  /// 2. Double recursion (f l + v + f r) creating _After frames
  /// 3. The flatten optimization (optimize_frame_push_args) that adds
  /// std::move to _Enter frame pushes
  ///
  /// If an _After frame stores a raw pointer (d_a0.get()) to a child
  /// of an owned tree, and the tree is destroyed at the end of the
  /// _Enter handler, the raw pointer would dangle.
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> a0;
      uint64_t a1;
      std::unique_ptr<tree> a2;
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
          _dst->v_ = Node{_alt.a0 ? std::make_unique<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_unique<tree>() : nullptr};
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
      return tree(Node{std::make_unique<tree>(std::move(a0)), a1,
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
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
        _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                          std::move(_f.a0_1)});
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
        _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                          std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            f0(_f.a0, std::move(_result), _f.a1, _f.a2, std::move(_f._result));
      }
    }
    return _result;
  }

  /// TEST 1: Non-method tree traversal with double recursion.
  /// dummy ensures tree is NOT the first arg (avoiding methodification).
  /// tree is the second arg — should be owned if it doesn't escape.
  static uint64_t tree_sum_ext(uint64_t _x, const tree &t);
  static inline const uint64_t test_tree_sum = tree_sum_ext(
      UINT64_C(0),
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
  /// TEST 2: Same but with a more complex computation to prevent
  /// the optimizer from simplifying.
  static uint64_t tree_weighted(uint64_t _x, const tree &t, uint64_t depth);
  static inline const uint64_t test_tree_weighted = tree_weighted(
      UINT64_C(0),
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf())),
      UINT64_C(1));
  /// TEST 3: Deep tree traversal — more iterations, more frames.
  static tree make_left_spine(uint64_t n);
  static inline const uint64_t test_deep_tree =
      tree_sum_ext(UINT64_C(0), make_left_spine(UINT64_C(100)));
  /// TEST 4: Tree traversal where both recursive calls use
  /// different subtrees — _After frame must hold one while
  /// processing the other.
  static uint64_t tree_collect(uint64_t _x, const tree &t);
  static inline const uint64_t test_collect = tree_collect(
      UINT64_C(0),
      tree::node(
          tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                     UINT64_C(10), tree::leaf()),
          UINT64_C(20),
          tree::node(tree::leaf(), UINT64_C(30),
                     tree::node(tree::leaf(), UINT64_C(40), tree::leaf()))));
  /// TEST 5: Tree function where the tree is consumed (not
  /// used after recursive calls) — maximally owned.
  static uint64_t tree_flatten(uint64_t _x, const tree &t);
  static inline const uint64_t test_flatten = tree_flatten(
      UINT64_C(0),
      tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                 UINT64_C(3),
                 tree::node(tree::leaf(), UINT64_C(5), tree::leaf())));
  /// TEST 6: Pass tree as a higher-order function argument
  /// to prevent methodification completely.
  static uint64_t tree_size_via_fold(const tree &t);
  static inline const uint64_t test_fold_size = tree_size_via_fold(tree::node(
      tree::node(tree::leaf(), UINT64_C(1), tree::leaf()), UINT64_C(2),
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(4), tree::leaf())));
};

#endif // INCLUDED_MEM_SAFETY_PROBE8
