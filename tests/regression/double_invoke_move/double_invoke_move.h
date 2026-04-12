#ifndef INCLUDED_DOUBLE_INVOKE_MOVE
#define INCLUDED_DOUBLE_INVOKE_MOVE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct DoubleInvokeMove {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf &) -> T1 { return f; },
                   [&](const typename tree::Node &_args) -> T1 {
                     return f0(_args.d_a0, tree_rect<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rect<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf &) -> T1 { return f; },
                   [&](const typename tree::Node &_args) -> T1 {
                     return f0(_args.d_a0, tree_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  /// wrap_with takes TWO args. Partial application creates a closure.
  /// Since t is stored in a constructor, wrap_with takes t as owned (by value).
  static std::shared_ptr<tree> wrap_with(std::shared_ptr<tree> t,
                                         const unsigned int v);
  __attribute__((pure)) static unsigned int
  left_value(const std::shared_ptr<tree> &t);
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
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<std::shared_ptr<tree>(unsigned int)> f =
          [=](unsigned int _x0) mutable -> std::shared_ptr<tree> {
        return wrap_with(t, _x0);
      };
      std::shared_ptr<tree> w1 = f(0u);
      std::shared_ptr<tree> w2 = f(1u);
      return (left_value(std::move(w1)) + left_value(std::move(w2)));
    }();
  }();
};

#endif // INCLUDED_DOUBLE_INVOKE_MOVE
