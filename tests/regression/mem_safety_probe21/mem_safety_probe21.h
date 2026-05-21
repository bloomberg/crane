#ifndef INCLUDED_MEM_SAFETY_PROBE21
#define INCLUDED_MEM_SAFETY_PROBE21

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe21 {
  /// Probe 21: Loopified recursion with constructed-value arguments.
  ///
  /// Attack vectors:
  /// 1. Recursive calls where the tree argument is a CONSTRUCTOR CALL
  /// (not the same parameter). The loopifier stores raw pointers to
  /// tree parameters. If the recursive call creates a temporary tree,
  /// the pointer to the temporary may dangle after the temporary dies.
  /// 2. Non-tail recursive calls where both the original parameter AND
  /// a constructed tree are used, requiring frame saves and moves.
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
  /// TEST 1: Tail-recursive function where the recursive call takes
  /// a constructed tree. The loopifier must store the new tree
  /// somewhere that outlives the iteration.
  static uint64_t grow_and_sum(tree t, uint64_t n);
  static inline const uint64_t test_grow_and_sum =
      grow_and_sum(tree::leaf(), UINT64_C(3));
  /// TEST 2: Non-tail recursive with constructed tree argument.
  /// The recursive call creates a new tree AND uses the original.
  static uint64_t double_grow(tree t, uint64_t n);
  static inline const uint64_t test_double_grow = double_grow(
      tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(2));
  /// TEST 3: Two recursive calls, one with original tree, one with
  /// constructed tree.
  static uint64_t branch_grow(const tree &t, uint64_t n);
  static inline const uint64_t test_branch_grow = branch_grow(
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(2));
  /// TEST 4: Recursive call where the tree argument is built from
  /// MULTIPLE constructor calls with the original tree embedded.
  static uint64_t embed_grow(tree t, uint64_t n);
  static inline const uint64_t test_embed_grow =
      embed_grow(tree::leaf(), UINT64_C(2));
  /// TEST 5: Accumulator pattern with tree building.
  static tree accum_tree(tree acc, uint64_t n);
  static inline const uint64_t test_accum_tree =
      tree_sum(accum_tree(tree::leaf(), UINT64_C(4)));

  /// TEST 6: CPS-like pattern where the continuation builds a tree.
  static uint64_t cps_sum(
      const tree &t,
      std::function<uint64_t(uint64_t)>
          k) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      std::function<uint64_t(uint64_t)> k;
      const tree *t;
    };

    using _Frame = std::variant<_Enter>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{k, &t});
    /// Loopified cps_sum: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      std::function<uint64_t(uint64_t)> k = std::move(_f.k);
      const tree &t = *_f.t;
      if (std::holds_alternative<typename tree::Leaf>(t.v())) {
        _result = k(UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        _stack.emplace_back(_Enter{[=](uint64_t lsum) mutable {
                                     return cps_sum(
                                         a2_value, [=](uint64_t rsum) mutable {
                                           return k(((lsum + a1) + rsum));
                                         });
                                   },
                                   a0.get()});
      }
    }
    return _result;
  }

  static inline const uint64_t test_cps_sum =
      cps_sum(tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                         UINT64_C(2),
                         tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
              [](uint64_t n) { return n; });
  /// TEST 7: Mutually-referencing recursive call with tree
  /// construction at each level.
  static uint64_t weave(tree t1, tree t2, uint64_t n);
  static inline const uint64_t test_weave =
      weave(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
            tree::node(tree::leaf(), UINT64_C(2), tree::leaf()), UINT64_C(2));
  /// TEST 8: Deep nesting with tree_sum at each level before recursion.
  static uint64_t sum_and_grow(tree t, uint64_t n);
  static inline const uint64_t test_sum_and_grow = sum_and_grow(
      tree::node(tree::leaf(), UINT64_C(1), tree::leaf()), UINT64_C(3));
};

#endif // INCLUDED_MEM_SAFETY_PROBE21
