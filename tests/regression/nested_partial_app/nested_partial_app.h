#ifndef INCLUDED_NESTED_PARTIAL_APP
#define INCLUDED_NESTED_PARTIAL_APP

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

struct NestedPartialApp {
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
        Overloaded{[&](const typename tree::Leaf) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
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
        Overloaded{[&](const typename tree::Leaf) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree> &t);
  /// 3-argument function: builds Node(t1, n, t2).
  static std::shared_ptr<tree> build_node(std::shared_ptr<tree> t1,
                                          const unsigned int n,
                                          std::shared_ptr<tree> t2);
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
      std::shared_ptr<tree> t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      std::function<std::shared_ptr<tree>(unsigned int, std::shared_ptr<tree>)>
          g = [=](unsigned int _x0, const std::shared_ptr<tree> &_x1) mutable
          -> std::shared_ptr<tree> { return build_node(t1, _x0, _x1); };
      std::function<std::shared_ptr<tree>(std::shared_ptr<tree>)> h =
          [=](std::shared_ptr<tree> _pa0) mutable { return g(42u, _pa0); };
      std::shared_ptr<tree> r1 = h(tree::node(tree::leaf(), 1u, tree::leaf()));
      std::shared_ptr<tree> r2 = h(tree::node(tree::leaf(), 2u, tree::leaf()));
      return (tree_sum(std::move(r1)) + tree_sum(std::move(r2)));
    }();
  }();
  /// Variation: use intermediate partial app g twice before further
  /// partial application. Tests if g's capture of t1 survives.
  static inline const unsigned int nested_partial_reuse = []() {
    return []() {
      std::shared_ptr<tree> t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      std::function<std::shared_ptr<tree>(unsigned int, std::shared_ptr<tree>)>
          g = [=](unsigned int _x0, const std::shared_ptr<tree> &_x1) mutable
          -> std::shared_ptr<tree> { return build_node(t1, _x0, _x1); };
      std::function<std::shared_ptr<tree>(std::shared_ptr<tree>)> h1 =
          [=](std::shared_ptr<tree> _pa0) mutable { return g(42u, _pa0); };
      std::function<std::shared_ptr<tree>(std::shared_ptr<tree>)> h2 =
          [=](std::shared_ptr<tree> _pa0) mutable { return g(99u, _pa0); };
      std::shared_ptr<tree> r1 = h1(tree::node(tree::leaf(), 1u, tree::leaf()));
      std::shared_ptr<tree> r2 = h2(tree::node(tree::leaf(), 2u, tree::leaf()));
      return (tree_sum(std::move(r1)) + tree_sum(std::move(r2)));
    }();
  }();
  /// Variation: 4-argument function, triple nesting.
  __attribute__((pure)) static unsigned int
  quad_fn(const std::shared_ptr<tree> &a, const unsigned int b,
          const unsigned int c, const std::shared_ptr<tree> &d);
  static inline const unsigned int triple_partial = []() {
    return []() {
      std::shared_ptr<tree> t = tree::node(tree::leaf(), 10u, tree::leaf());
      std::function<unsigned int(unsigned int, unsigned int,
                                 std::shared_ptr<tree>)>
          f1 = [=](unsigned int _x0, unsigned int _x1,
                   const std::shared_ptr<tree> &_x2) mutable -> unsigned int {
        return quad_fn(t, _x0, _x1, _x2);
      };
      std::function<unsigned int(unsigned int, std::shared_ptr<tree>)> f2 =
          [=](unsigned int _pa0, std::shared_ptr<tree> _pa1) mutable {
            return f1(20u, _pa0, _pa1);
          };
      std::function<unsigned int(std::shared_ptr<tree>)> f3 =
          [=](std::shared_ptr<tree> _pa0) mutable { return f2(30u, _pa0); };
      unsigned int r1 = f3(tree::node(tree::leaf(), 1u, tree::leaf()));
      unsigned int r2 = f3(tree::node(tree::leaf(), 2u, tree::leaf()));
      return (r1 + r2);
    }();
  }();
};

#endif // INCLUDED_NESTED_PARTIAL_APP
