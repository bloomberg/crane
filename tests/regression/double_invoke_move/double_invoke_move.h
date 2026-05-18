#ifndef INCLUDED_DOUBLE_INVOKE_MOVE
#define INCLUDED_DOUBLE_INVOKE_MOVE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct DoubleInvokeMove {
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

  /// wrap_with takes TWO args. Partial application creates a closure.
  /// Since t is stored in a constructor, wrap_with takes t as owned (by value).
  static tree wrap_with(tree t, uint64_t v);
  static uint64_t left_value(const tree &t);
  /// BUG HYPOTHESIS: partial application wrap_with t creates a & lambda.
  /// If t is marked dead-after (not used in continuation), std::move(t)
  /// appears INSIDE the lambda body. First call moves t, second call
  /// gets null → creates a node with null left child → left_value crashes.
  ///
  /// Expected: left_value(Node(t, 0, Leaf)) + left_value(Node(t, 1, Leaf))
  /// = left_value(t).left + left_value(t).left
  /// = 20 + 20 = 40  (the left_value of t = Node(Node(Leaf,10,Leaf),20,...) is
  /// 10, but left_value looks at l's first child... Actually let me
  /// recalculate.
  ///
  /// t = Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf))
  /// w1 = Node(t, 0, Leaf)
  /// left_value w1: match w1 → Node l v r where l=t, v=0, r=Leaf
  /// match l=t → Node l2 v2 r2 where l2=Node(Leaf,10,Leaf), v2=20, r2=...
  /// → v2 = 20
  /// w2 = Node(t, 1, Leaf)  if t is still valid
  /// left_value w2: same as w1 → 20
  /// Total: 40
  static inline const uint64_t bug_double_invoke = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      std::function<tree(uint64_t)> f = [=](uint64_t _x0) mutable -> tree {
        return wrap_with(t, _x0);
      };
      tree w1 = f(UINT64_C(0));
      tree w2 = f(UINT64_C(1));
      return (left_value(std::move(w1)) + left_value(std::move(w2)));
    }();
  }();
};

#endif // INCLUDED_DOUBLE_INVOKE_MOVE
