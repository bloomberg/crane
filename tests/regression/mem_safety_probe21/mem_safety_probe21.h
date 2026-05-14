#ifndef INCLUDED_MEM_SAFETY_PROBE21
#define INCLUDED_MEM_SAFETY_PROBE21

#include <functional>
#include <memory>
#include <optional>
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
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
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
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  static unsigned int tree_sum(const tree &t);
  /// TEST 1: Tail-recursive function where the recursive call takes
  /// a constructed tree. The loopifier must store the new tree
  /// somewhere that outlives the iteration.
  static unsigned int grow_and_sum(tree t, const unsigned int n);
  static inline const unsigned int test_grow_and_sum =
      grow_and_sum(tree::leaf(), 3u);
  /// TEST 2: Non-tail recursive with constructed tree argument.
  /// The recursive call creates a new tree AND uses the original.
  static unsigned int double_grow(tree t, const unsigned int n);
  static inline const unsigned int test_double_grow =
      double_grow(tree::node(tree::leaf(), 5u, tree::leaf()), 2u);
  /// TEST 3: Two recursive calls, one with original tree, one with
  /// constructed tree.
  static unsigned int branch_grow(const tree &t, const unsigned int n);
  static inline const unsigned int test_branch_grow =
      branch_grow(tree::node(tree::leaf(), 10u, tree::leaf()), 2u);
  /// TEST 4: Recursive call where the tree argument is built from
  /// MULTIPLE constructor calls with the original tree embedded.
  static unsigned int embed_grow(tree t, const unsigned int n);
  static inline const unsigned int test_embed_grow =
      embed_grow(tree::leaf(), 2u);
  /// TEST 5: Accumulator pattern with tree building.
  static tree accum_tree(tree acc, const unsigned int n);
  static inline const unsigned int test_accum_tree =
      tree_sum(accum_tree(tree::leaf(), 4u));

  /// TEST 6: CPS-like pattern where the continuation builds a tree.
  static unsigned int cps_sum(
      const tree &t,
      const std::function<unsigned int(unsigned int)>
          k) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      std::function<unsigned int(unsigned int)> k;
      const tree *t;
    };

    using _Frame = std::variant<_Enter>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter(k, &t));
    /// Loopified cps_sum: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      const std::function<unsigned int(unsigned int)> &k = _f.k;
      const tree &t = *(_f.t);
      if (std::holds_alternative<typename tree::Leaf>(t.v())) {
        _result = k(0u);
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
        tree d_a0_value = *(d_a0);
        tree d_a2_value = *(d_a2);
        _stack.emplace_back(_Enter(
            [=](const unsigned int lsum) mutable {
              return cps_sum(d_a2_value, [=](const unsigned int rsum) mutable {
                return k(((lsum + d_a1) + rsum));
              });
            },
            d_a0.get()));
      }
    }
    return _result;
  }

  static inline const unsigned int test_cps_sum =
      cps_sum(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                         tree::node(tree::leaf(), 3u, tree::leaf())),
              [](const unsigned int n) { return n; });
  /// TEST 7: Mutually-referencing recursive call with tree
  /// construction at each level.
  static unsigned int weave(tree t1, tree t2, const unsigned int n);
  static inline const unsigned int test_weave =
      weave(tree::node(tree::leaf(), 1u, tree::leaf()),
            tree::node(tree::leaf(), 2u, tree::leaf()), 2u);
  /// TEST 8: Deep nesting with tree_sum at each level before recursion.
  static unsigned int sum_and_grow(tree t, const unsigned int n);
  static inline const unsigned int test_sum_and_grow =
      sum_and_grow(tree::node(tree::leaf(), 1u, tree::leaf()), 3u);
};

#endif // INCLUDED_MEM_SAFETY_PROBE21
