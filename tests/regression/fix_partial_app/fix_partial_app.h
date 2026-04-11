#ifndef INCLUDED_FIX_PARTIAL_APP
#define INCLUDED_FIX_PARTIAL_APP

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

struct FixPartialApp {
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

  /// count_nodes: counts nodes in a tree. Will be partially applied.
  __attribute__((pure)) static unsigned int
  count_nodes(const std::shared_ptr<tree> &t, const unsigned int base);
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
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 0u, tree::leaf()), 0u,
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
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 0u, tree::leaf()), 0u,
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
  static std::shared_ptr<tree> tree_map(F0 &&f,
                                        const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{
            [](const typename tree::Leaf) -> std::shared_ptr<tree> {
              return tree::leaf();
            },
            [&](const typename tree::Node _args) -> std::shared_ptr<tree> {
              return tree::node(tree_map(f, _args.d_a0), f(_args.d_a1),
                                tree_map(f, _args.d_a2));
            }},
        t->v());
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree> &t);
  /// Partial app of tree_map: g := tree_map (fun x => x + 1)
  /// Then apply g to two different trees.
  /// If the closure for g captures the function arg by &, it could dangle.
  static inline const unsigned int map_partial_bug = []() {
    std::function<std::shared_ptr<tree>(std::shared_ptr<tree>)> g =
        [](const std::shared_ptr<tree> &_x0) -> std::shared_ptr<tree> {
      return tree_map([](unsigned int x) { return (x + 1u); }, _x0);
    };
    std::shared_ptr<tree> t1 = tree::node(tree::leaf(), 10u, tree::leaf());
    std::shared_ptr<tree> t2 = tree::node(tree::leaf(), 20u, tree::leaf());
    return (tree_sum(g(std::move(t1))) + tree_sum(g(std::move(t2))));
  }();
};

#endif // INCLUDED_FIX_PARTIAL_APP
