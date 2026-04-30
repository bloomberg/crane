#ifndef INCLUDED_NESTED_PARTIAL_APP
#define INCLUDED_NESTED_PARTIAL_APP

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NestedPartialApp {
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

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->d_v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a2)
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack;
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
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
  /// 3-argument function: builds Node(t1, n, t2).
  static tree build_node(tree t1, unsigned int n, tree t2);
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
  static inline const unsigned int nested_partial_bug = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      std::function<tree(unsigned int, tree)> g =
          [=](unsigned int _x0, tree _x1) mutable -> tree {
        return build_node(t1, _x0, _x1);
      };
      std::function<tree(tree)> h = [=](tree _pa0) mutable {
        return g(42u, _pa0);
      };
      tree r1 = h(tree::node(tree::leaf(), 1u, tree::leaf()));
      tree r2 = h(tree::node(tree::leaf(), 2u, tree::leaf()));
      return (tree_sum(std::move(r1)) + tree_sum(std::move(r2)));
    }();
  }();
  /// Variation: use intermediate partial app g twice before further
  /// partial application. Tests if g's capture of t1 survives.
  static inline const unsigned int nested_partial_reuse = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      std::function<tree(unsigned int, tree)> g =
          [=](unsigned int _x0, tree _x1) mutable -> tree {
        return build_node(t1, _x0, _x1);
      };
      std::function<tree(tree)> h1 = [=](tree _pa0) mutable {
        return g(42u, _pa0);
      };
      std::function<tree(tree)> h2 = [=](tree _pa0) mutable {
        return g(99u, _pa0);
      };
      tree r1 = h1(tree::node(tree::leaf(), 1u, tree::leaf()));
      tree r2 = h2(tree::node(tree::leaf(), 2u, tree::leaf()));
      return (tree_sum(std::move(r1)) + tree_sum(std::move(r2)));
    }();
  }();
  /// Variation: 4-argument function, triple nesting.
  static unsigned int quad_fn(const tree &a, const unsigned int &b,
                              const unsigned int &c, const tree &d);
  static inline const unsigned int triple_partial = []() {
    return []() {
      tree t = tree::node(tree::leaf(), 10u, tree::leaf());
      std::function<unsigned int(unsigned int, unsigned int, tree)> f1 =
          [=](unsigned int _x0, unsigned int _x1,
              tree _x2) mutable -> unsigned int {
        return quad_fn(t, _x0, _x1, _x2);
      };
      std::function<unsigned int(unsigned int, tree)> f2 =
          [=](unsigned int _pa0, tree _pa1) mutable {
            return f1(20u, _pa0, _pa1);
          };
      std::function<unsigned int(tree)> f3 = [=](tree _pa0) mutable {
        return f2(30u, _pa0);
      };
      unsigned int r1 = f3(tree::node(tree::leaf(), 1u, tree::leaf()));
      unsigned int r2 = f3(tree::node(tree::leaf(), 2u, tree::leaf()));
      return (r1 + r2);
    }();
  }();
};

#endif // INCLUDED_NESTED_PARTIAL_APP
