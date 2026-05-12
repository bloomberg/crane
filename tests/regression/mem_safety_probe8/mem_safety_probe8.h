#ifndef INCLUDED_MEM_SAFETY_PROBE8
#define INCLUDED_MEM_SAFETY_PROBE8

#include <functional>
#include <memory>
#include <optional>
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

  /// TEST 1: Non-method tree traversal with double recursion.
  /// dummy ensures tree is NOT the first arg (avoiding methodification).
  /// tree is the second arg — should be owned if it doesn't escape.
  static unsigned int tree_sum_ext(const unsigned int _x, const tree &t);
  static inline const unsigned int test_tree_sum = tree_sum_ext(
      0u, tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf())));
  /// TEST 2: Same but with a more complex computation to prevent
  /// the optimizer from simplifying.
  static unsigned int tree_weighted(const unsigned int _x, const tree &t,
                                    const unsigned int depth);
  static inline const unsigned int test_tree_weighted =
      tree_weighted(0u,
                    tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                               tree::node(tree::leaf(), 30u, tree::leaf())),
                    1u);
  /// TEST 3: Deep tree traversal — more iterations, more frames.
  static tree make_left_spine(const unsigned int n);
  static inline const unsigned int test_deep_tree =
      tree_sum_ext(0u, make_left_spine(100u));
  /// TEST 4: Tree traversal where both recursive calls use
  /// different subtrees — _After frame must hold one while
  /// processing the other.
  static unsigned int tree_collect(const unsigned int _x, const tree &t);
  static inline const unsigned int test_collect = tree_collect(
      0u, tree::node(tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                                tree::leaf()),
                     20u,
                     tree::node(tree::leaf(), 30u,
                                tree::node(tree::leaf(), 40u, tree::leaf()))));
  /// TEST 5: Tree function where the tree is consumed (not
  /// used after recursive calls) — maximally owned.
  static unsigned int tree_flatten(const unsigned int _x, const tree &t);
  static inline const unsigned int test_flatten = tree_flatten(
      0u, tree::node(tree::node(tree::leaf(), 2u, tree::leaf()), 3u,
                     tree::node(tree::leaf(), 5u, tree::leaf())));
  /// TEST 6: Pass tree as a higher-order function argument
  /// to prevent methodification completely.
  static unsigned int tree_size_via_fold(const tree &t);
  static inline const unsigned int test_fold_size = tree_size_via_fold(
      tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                 tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 4u,
                            tree::leaf())));
};

#endif // INCLUDED_MEM_SAFETY_PROBE8
