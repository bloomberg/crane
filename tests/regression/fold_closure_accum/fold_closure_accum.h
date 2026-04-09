#ifndef INCLUDED_FOLD_CLOSURE_ACCUM
#define INCLUDED_FOLD_CLOSURE_ACCUM

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, t_A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{
            [&](const typename List<t_A>::Nil _args) -> T1 { return a0; },
            [&](const typename List<t_A>::Cons _args) -> T1 {
              return f(_args.d_a0, _args.d_a1->template fold_right<T1>(f, a0));
            }},
        this->v());
  }
};

struct FoldClosureAccum {
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
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
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
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  /// Sum all values in a tree.
  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree> &t);
  /// Build a composed function by folding over a list of trees.
  /// Each step takes the accumulated function and the current tree,
  /// producing a new function that adds tree_sum of the current tree
  /// to the accumulated function's result.
  ///
  /// BUG HYPOTHESIS: Each fold step creates a closure &acc, &t that
  /// captures the previous closure (acc) and the current tree (t).
  /// If captures are by reference, the previous closure is stack-local
  /// and dies when the fold step returns, creating a dangling chain.
  __attribute__((pure)) static unsigned int
  compose_adders(const std::shared_ptr<List<std::shared_ptr<tree>>> &trees,
                 const unsigned int _x0);
  /// Test: compose adders from 3 trees.
  /// t1 sums to 10, t2 sums to 20, t3 sums to 30.
  /// compose_adders t1; t2; t3 x = x + 30 + 20 + 10 = x + 60
  /// Expected: compose_adders t1; t2; t3 0 = 60
  static inline const unsigned int fold_bug = []() {
    std::shared_ptr<tree> t1 = tree::node(tree::leaf(), 10u, tree::leaf());
    std::shared_ptr<tree> t2 = tree::node(tree::leaf(), 20u, tree::leaf());
    std::shared_ptr<tree> t3 = tree::node(tree::leaf(), 30u, tree::leaf());
    return compose_adders(
        List<std::shared_ptr<tree>>::cons(
            t1, List<std::shared_ptr<tree>>::cons(
                    t2, List<std::shared_ptr<tree>>::cons(
                            t3, List<std::shared_ptr<tree>>::nil()))),
        0u);
  }();
  /// Test with non-zero starting value.
  /// Expected: compose_adders t1; t2; t3 7 = 67
  static inline const unsigned int fold_bug_offset = []() {
    std::shared_ptr<tree> t1 = tree::node(tree::leaf(), 10u, tree::leaf());
    std::shared_ptr<tree> t2 = tree::node(tree::leaf(), 20u, tree::leaf());
    std::shared_ptr<tree> t3 = tree::node(tree::leaf(), 30u, tree::leaf());
    return compose_adders(
        List<std::shared_ptr<tree>>::cons(
            t1, List<std::shared_ptr<tree>>::cons(
                    t2, List<std::shared_ptr<tree>>::cons(
                            t3, List<std::shared_ptr<tree>>::nil()))),
        7u);
  }();
  /// Invoke the composed function twice — tests if closures survive
  /// multiple invocations.
  static inline const unsigned int fold_bug_double = []() {
    return []() {
      std::shared_ptr<tree> t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      std::shared_ptr<tree> t2 = tree::node(tree::leaf(), 20u, tree::leaf());
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return compose_adders(
            List<std::shared_ptr<tree>>::cons(
                t1, List<std::shared_ptr<tree>>::cons(
                        t2, List<std::shared_ptr<tree>>::nil())),
            _x0);
      };
      return (f(0u) + f(100u));
    }();
  }();
};

#endif // INCLUDED_FOLD_CLOSURE_ACCUM
