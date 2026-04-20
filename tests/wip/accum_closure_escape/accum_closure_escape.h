#ifndef INCLUDED_ACCUM_CLOSURE_ESCAPE
#define INCLUDED_ACCUM_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct AccumClosureEscape {
  /// This test explores closure escape through ACCUMULATOR patterns,
  /// which are different from the direct-return-in-constructor pattern
  /// tested by the other wip tests.
  ///
  /// Key difference: closures are built up in an accumulator during
  /// recursion. Each recursive step adds a new closure to a list.
  /// The closures capture pattern variables from the current match
  /// scope, which may be references into shared_ptr nodes.
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::shared_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist<t_A>> mynil() {
      return std::make_shared<mylist<t_A>>(Mynil{});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
      return std::make_shared<mylist<t_A>>(Mycons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, std::shared_ptr<mylist<t_A>> &&a1) {
      return std::make_shared<mylist<t_A>>(
          Mycons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<mylist<t_A>>
    mylist_append(std::shared_ptr<mylist<t_A>> l2) const {
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(this->v())) {
        return l2;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(this->v());
        return mylist<t_A>::mycons(d_a0, d_a1->mylist_append(l2));
      }
    }

    template <typename T1, MapsTo<T1, t_A, std::shared_ptr<mylist<t_A>>, T1> F1>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(this->v());
        return f0(d_a0, d_a1, d_a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, std::shared_ptr<mylist<t_A>>, T1> F1>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(this->v());
        return f0(d_a0, d_a1, d_a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  /// A simple tree for supplying values.
  struct tree {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(TLeaf _v) : d_v_(_v) {}

    explicit tree(TNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> tleaf() {
      return std::make_shared<tree>(TLeaf{});
    }

    static std::shared_ptr<tree> tnode(const std::shared_ptr<tree> &a0,
                                       unsigned int a1,
                                       const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(TNode{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> tnode(std::shared_ptr<tree> &&a0,
                                       unsigned int a1,
                                       std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          TNode{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Build closures from TREE traversal: tree nodes become closures.
    /// Each closure captures pattern variables from tree match.
    std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>>
    tree_to_adders() const {
      if (std::holds_alternative<typename tree::TLeaf>(this->v())) {
        return mylist<std::function<unsigned int(unsigned int)>>::mynil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::TNode>(this->v());
        return mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](const unsigned int x) mutable { return (d_a1 + x); },
            d_a0->tree_to_adders()->mylist_append(d_a2->tree_to_adders()));
      }
    }

    std::shared_ptr<mylist<unsigned int>> tree_to_list() const {
      if (std::holds_alternative<typename tree::TLeaf>(this->v())) {
        return mylist<unsigned int>::mynil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::TNode>(this->v());
        return mylist<unsigned int>::mycons(
            d_a1, d_a0->tree_to_list()->mylist_append(d_a2->tree_to_list()));
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                  std::shared_ptr<tree>, T1>
                               F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::TLeaf>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::TNode>(this->v());
        return f0(d_a0, d_a0->template tree_rec<T1>(f, f0), d_a1, d_a2,
                  d_a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                  std::shared_ptr<tree>, T1>
                               F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::TLeaf>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::TNode>(this->v());
        return f0(d_a0, d_a0->template tree_rect<T1>(f, f0), d_a1, d_a2,
                  d_a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  /// Fold-left that builds a closure from each element.
  ///
  /// SIMPLE LAMBDA VERSION: Each closure fun x => h + x captures
  /// h from the pattern match. These are simple lambdas, so they
  /// should capture by =.
  static std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>>
  build_adders(
      const std::shared_ptr<mylist<unsigned int>> &l,
      std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>> acc);
  /// Apply first closure from the list.
  __attribute__((pure)) static unsigned int apply_first(
      const std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>>
          &fns,
      const unsigned int x);
  /// Apply all closures and sum.
  __attribute__((pure)) static unsigned int apply_all_sum(
      const std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>>
          &fns,
      const unsigned int x);
  /// test1: build_adders 10, 20, 30  = 30+_, 20+_, 10+_ (reversed)
  /// apply_first result 5 = 30 + 5 = 35
  static inline const unsigned int test1 = []() {
    std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>> fns =
        build_adders(
            mylist<unsigned int>::mycons(
                10u, mylist<unsigned int>::mycons(
                         20u, mylist<unsigned int>::mycons(
                                  30u, mylist<unsigned int>::mynil()))),
            mylist<std::function<unsigned int(unsigned int)>>::mynil());
    return apply_first(std::move(fns), 5u);
  }();
  /// test2: apply all closures: (30+5) + (20+5) + (10+5) = 35+25+15 = 75
  static inline const unsigned int test2 = []() {
    std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>> fns =
        build_adders(
            mylist<unsigned int>::mycons(
                10u, mylist<unsigned int>::mycons(
                         20u, mylist<unsigned int>::mycons(
                                  30u, mylist<unsigned int>::mynil()))),
            mylist<std::function<unsigned int(unsigned int)>>::mynil());
    return apply_all_sum(std::move(fns), 5u);
  }();

  /// COMPOSE CLOSURES: Each step builds a composed function.
  /// This creates closures that capture OTHER closures.
  __attribute__((pure)) static unsigned int
  compose_from_list(const std::shared_ptr<mylist<unsigned int>> &l, F1 &&acc,
                    const unsigned int _x0) {
    return [&]() -> std::function<unsigned int(unsigned int)> {
      if (std::holds_alternative<typename mylist<unsigned int>::Mynil>(
              l->v())) {
        return acc;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<unsigned int>::Mycons>(l->v());
        return [=](unsigned int _x0) mutable -> unsigned int {
          return compose_from_list(
              d_a1,
              [=](const unsigned int x) mutable { return acc((d_a0 + x)); },
              _x0);
        };
      }
    }()(_x0);
  }

  /// test3: compose_from_list 10, 20, 30 id
  /// = fun x => id (10 + (20 + (30 + x)))
  /// = fun x => 60 + x
  /// test3 = 60 + 7 = 67
  static inline const unsigned int test3 = compose_from_list(
      mylist<unsigned int>::mycons(
          10u, mylist<unsigned int>::mycons(
                   20u, mylist<unsigned int>::mycons(
                            30u, mylist<unsigned int>::mynil()))),
      [](const unsigned int x) { return x; }, 7u);
  /// test4: Tree (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf))
  /// Closures: 20+_, 10+_, 30+_
  /// apply_all_sum with 5: (20+5) + (10+5) + (30+5) = 25+15+35 = 75
  static inline const unsigned int test4 = []() {
    std::shared_ptr<tree> t =
        tree::tnode(tree::tnode(tree::tleaf(), 10u, tree::tleaf()), 20u,
                    tree::tnode(tree::tleaf(), 30u, tree::tleaf()));
    return apply_all_sum(std::move(t)->tree_to_adders(), 5u);
  }();
  /// Store a closure and then clobber the stack before using it.
  static inline const unsigned int test5 = []() {
    std::shared_ptr<tree> t = tree::tnode(
        tree::tnode(tree::tleaf(), 42u, tree::tleaf()), 100u, tree::tleaf());
    std::shared_ptr<mylist<std::function<unsigned int(unsigned int)>>> fns =
        std::move(t)->tree_to_adders();
    return apply_first(std::move(fns), 0u);
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_ESCAPE
