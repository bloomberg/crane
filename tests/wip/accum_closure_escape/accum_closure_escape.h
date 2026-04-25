#ifndef INCLUDED_ACCUM_CLOSURE_ESCAPE
#define INCLUDED_ACCUM_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

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
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist<t_A>(Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist<t_A>(
            Mycons{clone_as_value<t_A>(d_a0),
                   clone_as_value<std::unique_ptr<mylist<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) mylist<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist<_CloneT0>(typename mylist<_CloneT0>::Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist<_CloneT0>(typename mylist<_CloneT0>::Mycons{
            clone_as_value<_CloneT0>(d_a0),
            clone_as_value<std::unique_ptr<mylist<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static mylist<t_A> mynil() { return mylist(Mynil{}); }

    __attribute__((pure)) static mylist<t_A> mycons(t_A a0,
                                                    const mylist<t_A> &a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> *operator->() { return this; }

    __attribute__((pure)) const mylist<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mylist<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) mylist<t_A> mylist_append(mylist<t_A> l2) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return l2;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return mylist<t_A>::mycons(d_a0, (*(d_a1)).mylist_append(l2));
      }
    }

    template <typename T1, MapsTo<T1, t_A, mylist<t_A>, T1> F1>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, mylist<t_A>, T1> F1>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Mycons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rect<T1>(f, f0));
      }
    }
  };

  /// A simple tree for supplying values.
  struct tree {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(TLeaf _v) : d_v_(_v) {}

    explicit tree(TNode _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<TLeaf>(_sv.v())) {
        return tree(TLeaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<TNode>(_sv.v());
        return tree(TNode{clone_as_value<std::unique_ptr<tree>>(d_a0), d_a1,
                          clone_as_value<std::unique_ptr<tree>>(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree tleaf() { return tree(TLeaf{}); }

    __attribute__((pure)) static tree tnode(const tree &a0, unsigned int a1,
                                            const tree &a2) {
      return tree(TNode{std::make_unique<tree>(a0.clone()), std::move(a1),
                        std::make_unique<tree>(a2.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree *operator->() { return this; }

    __attribute__((pure)) const tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Build closures from TREE traversal: tree nodes become closures.
    /// Each closure captures pattern variables from tree match.
    __attribute__((pure)) mylist<std::function<unsigned int(unsigned int)>>
    tree_to_adders() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
        return mylist<std::function<unsigned int(unsigned int)>>::mynil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::TNode>(_sv.v());
        tree d_a0_value = clone_as_value<AccumClosureEscape::tree>(d_a0);
        tree d_a2_value = clone_as_value<AccumClosureEscape::tree>(d_a2);
        return mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](const unsigned int &x) mutable { return (d_a1 + x); },
            d_a0_value.tree_to_adders().mylist_append(
                d_a2_value.tree_to_adders()));
      }
    }

    __attribute__((pure)) mylist<unsigned int> tree_to_list() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
        return mylist<unsigned int>::mynil();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::TNode>(_sv.v());
        return mylist<unsigned int>::mycons(
            d_a1,
            (*(d_a0)).tree_to_list().mylist_append((*(d_a2)).tree_to_list()));
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::TNode>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rec<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::TNode>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rect<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rect<T1>(f, f0));
      }
    }
  };

  /// Fold-left that builds a closure from each element.
  ///
  /// SIMPLE LAMBDA VERSION: Each closure fun x => h + x captures
  /// h from the pattern match. These are simple lambdas, so they
  /// should capture by =.
  __attribute__((pure)) static mylist<std::function<unsigned int(unsigned int)>>
  build_adders(const mylist<unsigned int> &l,
               mylist<std::function<unsigned int(unsigned int)>> acc);
  /// Apply first closure from the list.
  __attribute__((pure)) static unsigned int
  apply_first(const mylist<std::function<unsigned int(unsigned int)>> &fns,
              const unsigned int &x);
  /// Apply all closures and sum.
  __attribute__((pure)) static unsigned int
  apply_all_sum(const mylist<std::function<unsigned int(unsigned int)>> &fns,
                const unsigned int &x);
  /// test1: build_adders 10, 20, 30  = 30+_, 20+_, 10+_ (reversed)
  /// apply_first result 5 = 30 + 5 = 35
  static inline const unsigned int test1 = []() {
    mylist<std::function<unsigned int(unsigned int)>> fns = build_adders(
        mylist<unsigned int>::mycons(
            10u, mylist<unsigned int>::mycons(
                     20u, mylist<unsigned int>::mycons(
                              30u, mylist<unsigned int>::mynil()))),
        mylist<std::function<unsigned int(unsigned int)>>::mynil());
    return apply_first(fns, 5u);
  }();
  /// test2: apply all closures: (30+5) + (20+5) + (10+5) = 35+25+15 = 75
  static inline const unsigned int test2 = []() {
    mylist<std::function<unsigned int(unsigned int)>> fns = build_adders(
        mylist<unsigned int>::mycons(
            10u, mylist<unsigned int>::mycons(
                     20u, mylist<unsigned int>::mycons(
                              30u, mylist<unsigned int>::mynil()))),
        mylist<std::function<unsigned int(unsigned int)>>::mynil());
    return apply_all_sum(fns, 5u);
  }();

  /// COMPOSE CLOSURES: Each step builds a composed function.
  /// This creates closures that capture OTHER closures.
  __attribute__((pure)) static unsigned int
  compose_from_list(const mylist<unsigned int> &l,
                    const std::function<unsigned int(unsigned int)> acc,
                    unsigned int _x0) {
    return [=]() mutable -> std::function<unsigned int(unsigned int)> {
      if (std::holds_alternative<typename mylist<unsigned int>::Mynil>(l.v())) {
        return acc;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<unsigned int>::Mycons>(l.v());
        mylist<unsigned int> d_a1_value =
            clone_as_value<AccumClosureEscape::mylist<unsigned int>>(d_a1);
        return [=](unsigned int _x0) mutable -> unsigned int {
          return compose_from_list(
              d_a1_value,
              [=](const unsigned int &x) mutable { return acc((d_a0 + x)); },
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
      [](unsigned int x) { return x; }, 7u);
  /// test4: Tree (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf))
  /// Closures: 20+_, 10+_, 30+_
  /// apply_all_sum with 5: (20+5) + (10+5) + (30+5) = 25+15+35 = 75
  static inline const unsigned int test4 = []() {
    tree t = tree::tnode(tree::tnode(tree::tleaf(), 10u, tree::tleaf()), 20u,
                         tree::tnode(tree::tleaf(), 30u, tree::tleaf()));
    return apply_all_sum(t.tree_to_adders(), 5u);
  }();
  /// Store a closure and then clobber the stack before using it.
  static inline const unsigned int test5 = []() {
    tree t = tree::tnode(tree::tnode(tree::tleaf(), 42u, tree::tleaf()), 100u,
                         tree::tleaf());
    mylist<std::function<unsigned int(unsigned int)>> fns = t.tree_to_adders();
    return apply_first(fns, 0u);
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_ESCAPE
