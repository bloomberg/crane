#ifndef INCLUDED_FIX_PARTIAL_APP
#define INCLUDED_FIX_PARTIAL_APP

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct FixPartialApp {
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

  /// count_nodes: counts nodes in a tree. Will be partially applied.
  static unsigned int count_nodes(const tree &t, unsigned int base);
  /// BUG HYPOTHESIS: Partially applying a fixpoint.
  /// f := count_nodes big_tree creates a closure (nat -> nat).
  /// The closure captures the fixpoint AND the tree.
  /// If either is captured by &, it's a dangling reference.
  ///
  /// big_tree = Node(Node(Leaf,0,Leaf), 0, Node(Leaf,0,Leaf))
  /// count_nodes big_tree 0 = count_nodes left (count_nodes right (0+1))
  /// = count_nodes left (count_nodes right 1)
  /// = count_nodes Leaf (count_nodes Leaf (1+1))
  /// = count_nodes Leaf (count_nodes Leaf 2)
  /// = count_nodes Leaf 2 = 2
  /// Wait that's wrong. Let me recalculate:
  /// count_nodes (Node l v r) base = count_nodes l (count_nodes r (base + 1))
  ///
  /// tree = Node(Node(Leaf,0,Leaf), 0, Node(Leaf,0,Leaf))
  /// count_nodes tree 0
  /// = count_nodes (Node(Leaf,0,Leaf)) (count_nodes (Node(Leaf,0,Leaf)) (0+1))
  /// = count_nodes (Node(Leaf,0,Leaf)) (count_nodes (Node(Leaf,0,Leaf)) 1)
  ///
  /// count_nodes (Node(Leaf,0,Leaf)) 1
  /// = count_nodes Leaf (count_nodes Leaf (1+1))
  /// = count_nodes Leaf (count_nodes Leaf 2)
  /// = count_nodes Leaf 2
  /// = 2
  ///
  /// count_nodes (Node(Leaf,0,Leaf)) 2
  /// = count_nodes Leaf (count_nodes Leaf (2+1))
  /// = count_nodes Leaf 3
  /// = 3
  ///
  /// So count_nodes tree 0 = 3
  static inline const unsigned int fix_partial_bug = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 0u, tree::leaf()), 0u,
                          tree::node(tree::leaf(), 0u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return count_nodes(t, _x0);
      };
      return (f(0u) + f(100u));
    }();
  }();
  /// Same but store partial app in pair
  static inline const unsigned int fix_partial_pair = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 0u, tree::leaf()), 0u,
                          tree::node(tree::leaf(), 0u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return count_nodes(t, _x0);
      };
      std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
          std::make_pair(f, 42u);
      return (p.first(0u) + p.first(100u));
    }();
  }();

  /// More complex: partial app of tree_map, a structure-preserving function.
  template <MapsTo<unsigned int, unsigned int> F0>
  static tree tree_map(F0 &&f, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return tree::leaf();
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return tree::node(tree_map(f, *(d_a0)), f(d_a1), tree_map(f, *(d_a2)));
    }
  }

  static unsigned int tree_sum(const tree &t);
  /// Partial app of tree_map: g := tree_map (fun x => x + 1)
  /// Then apply g to two different trees.
  /// If the closure for g captures the function arg by &, it could dangle.
  static inline const unsigned int map_partial_bug = []() {
    std::function<tree(tree)> g = [](tree _x0) -> tree {
      return tree_map([](const unsigned int &x) { return (x + 1u); }, _x0);
    };
    tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
    tree t2 = tree::node(tree::leaf(), 20u, tree::leaf());
    return (tree_sum(g(std::move(t1))) + tree_sum(g(std::move(t2))));
  }();
};

#endif // INCLUDED_FIX_PARTIAL_APP
