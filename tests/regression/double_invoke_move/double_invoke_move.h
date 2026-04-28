#ifndef INCLUDED_DOUBLE_INVOKE_MOVE
#define INCLUDED_DOUBLE_INVOKE_MOVE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct DoubleInvokeMove {
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
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(
            Node{d_a0 ? std::make_unique<DoubleInvokeMove::tree>(d_a0->clone())
                      : nullptr,
                 d_a1,
                 d_a2 ? std::make_unique<DoubleInvokeMove::tree>(d_a2->clone())
                      : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
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

  /// wrap_with takes TWO args. Partial application creates a closure.
  /// Since t is stored in a constructor, wrap_with takes t as owned (by value).
  __attribute__((pure)) static tree wrap_with(tree t, unsigned int v);
  __attribute__((pure)) static unsigned int left_value(const tree &t);
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
  static inline const unsigned int bug_double_invoke = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                          tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<tree(unsigned int)> f =
          [=](unsigned int _x0) mutable -> tree { return wrap_with(t, _x0); };
      tree w1 = f(0u);
      tree w2 = f(1u);
      return (left_value(std::move(w1)) + left_value(std::move(w2)));
    }();
  }();
};

#endif // INCLUDED_DOUBLE_INVOKE_MOVE
