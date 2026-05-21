#ifndef INCLUDED_NESTED_PARTIAL_APP
#define INCLUDED_NESTED_PARTIAL_APP

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct NestedPartialApp {
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

  static uint64_t tree_sum(const tree &t);
  /// 3-argument function: builds Node(t1, n, t2).
  static tree build_node(tree t1, uint64_t n, tree t2);
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
  static inline const uint64_t nested_partial_bug = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      std::function<tree(uint64_t, tree)> g = [=](uint64_t _x0,
                                                  tree _x1) mutable -> tree {
        return build_node(t1, _x0, _x1);
      };
      std::function<tree(tree)> h = [=](tree _pa0) mutable {
        return g(UINT64_C(42), _pa0);
      };
      tree r1 = h(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()));
      tree r2 = h(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()));
      return (tree_sum(std::move(r1)) + tree_sum(std::move(r2)));
    }();
  }();
  /// Variation: use intermediate partial app g twice before further
  /// partial application. Tests if g's capture of t1 survives.
  static inline const uint64_t nested_partial_reuse = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      std::function<tree(uint64_t, tree)> g = [=](uint64_t _x0,
                                                  tree _x1) mutable -> tree {
        return build_node(t1, _x0, _x1);
      };
      std::function<tree(tree)> h1 = [=](tree _pa0) mutable {
        return g(UINT64_C(42), _pa0);
      };
      std::function<tree(tree)> h2 = [=](tree _pa0) mutable {
        return g(UINT64_C(99), _pa0);
      };
      tree r1 = h1(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()));
      tree r2 = h2(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()));
      return (tree_sum(std::move(r1)) + tree_sum(std::move(r2)));
    }();
  }();
  /// Variation: 4-argument function, triple nesting.
  static uint64_t quad_fn(const tree &a, uint64_t b, uint64_t c, const tree &d);
  static inline const uint64_t triple_partial = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      std::function<uint64_t(uint64_t, uint64_t, tree)> f1 =
          [=](uint64_t _x0, uint64_t _x1, tree _x2) mutable -> uint64_t {
        return quad_fn(t, _x0, _x1, _x2);
      };
      std::function<uint64_t(uint64_t, tree)> f2 = [=](uint64_t _pa0,
                                                       tree _pa1) mutable {
        return f1(UINT64_C(20), _pa0, _pa1);
      };
      std::function<uint64_t(tree)> f3 = [=](tree _pa0) mutable {
        return f2(UINT64_C(30), _pa0);
      };
      uint64_t r1 = f3(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()));
      uint64_t r2 = f3(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()));
      return (r1 + r2);
    }();
  }();
};

#endif // INCLUDED_NESTED_PARTIAL_APP
