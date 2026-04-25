#ifndef INCLUDED_CPS_CLOSURE_CHAIN
#define INCLUDED_CPS_CLOSURE_CHAIN

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

struct CpsClosureChain {
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
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(Node{clone_as_value<std::unique_ptr<tree>>(d_a0), d_a1,
                         clone_as_value<std::unique_ptr<tree>>(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(const tree &a0, unsigned int a1,
                                           const tree &a2) {
      return tree(Node{std::make_unique<tree>(a0.clone()), std::move(a1),
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

  /// CPS-style tree traversal that builds a deep chain of continuations.
  ///
  /// BUG HYPOTHESIS: Each recursive call creates a closure that captures
  /// n (from the pattern match on the current node) and k (the
  /// continuation from the caller). The chain of closures forms a
  /// linked-list-like structure on the heap via std::function copies.
  /// When the chain is finally invoked, each closure needs its captured
  /// n to still be valid.
  ///
  /// Unlike the fixpoint-escape tests in wip/, these are SIMPLE lambdas
  /// (not local fixpoints), so they should use = capture. The question
  /// is whether the = capture correctly copies all pattern variables,
  /// especially when the pattern match is on a shared_ptr type and the
  /// structured bindings are references.
  __attribute__((pure)) static unsigned int
  tree_sum_cps(const tree &t,
               const std::function<unsigned int(unsigned int)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return k(0u);
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      tree d_a0_value = clone_as_value<CpsClosureChain::tree>(d_a0);
      tree d_a2_value = clone_as_value<CpsClosureChain::tree>(d_a2);
      return tree_sum_cps(d_a0_value, [=](unsigned int left_sum) mutable {
        return tree_sum_cps(d_a2_value,
                            [=](const unsigned int &right_sum) mutable {
                              return k(((left_sum + d_a1) + right_sum));
                            });
      });
    }
  }

  __attribute__((pure)) static unsigned int tree_sum(const tree &t);
  /// Build a deep tree to stress the closure chain.
  __attribute__((pure)) static tree build_left(unsigned int n);
  __attribute__((pure)) static tree build_right(unsigned int n);
  __attribute__((pure)) static tree build_balanced(unsigned int n);
  /// Test: left-spine tree with 5 nodes: sum = 1+2+3+4+5 = 15
  static inline const unsigned int test_left = tree_sum(build_left(5u));
  /// Test: right-spine tree with 5 nodes: sum = 1+2+3+4+5 = 15
  static inline const unsigned int test_right = tree_sum(build_right(5u));
  /// Test: balanced tree depth 3: values 1,2,3 with structure
  /// Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 1 Leaf))
  /// 3
  /// (Node (Node Leaf 1 Leaf) 2 (Node Leaf 1 Leaf))
  /// sum = 4*1 + 2*2 + 1*3 = 11
  static inline const unsigned int test_balanced = tree_sum(build_balanced(3u));

  /// CPS fold: accumulates results through continuation chain.
  /// This creates closures that capture BOTH a pattern variable
  /// AND the accumulator function.
  template <MapsTo<unsigned int, unsigned int, unsigned int, unsigned int> F2>
  __attribute__((pure)) static unsigned int
  tree_fold_cps(const tree &t, unsigned int base, F2 &&combine,
                const std::function<unsigned int(unsigned int)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return k(base);
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      tree d_a0_value = clone_as_value<CpsClosureChain::tree>(d_a0);
      tree d_a2_value = clone_as_value<CpsClosureChain::tree>(d_a2);
      return tree_fold_cps(
          d_a0_value, base, combine, [=](unsigned int left_result) mutable {
            return tree_fold_cps(
                d_a2_value, base, combine,
                [=](const unsigned int &right_result) mutable {
                  return k(combine(left_result, d_a1, right_result));
                });
          });
    }
  }

  /// Test: fold with multiplication: each node multiplies (left + right + n)
  static inline const unsigned int test_fold = tree_fold_cps(
      tree::node(tree::node(tree::leaf(), 2u, tree::leaf()), 3u,
                 tree::node(tree::leaf(), 4u, tree::leaf())),
      1u,
      [](const unsigned int &l, const unsigned int &n, const unsigned int &r) {
        return ((l + n) + r);
      },
      [](unsigned int x) { return x; });
  /// Store CPS result in a pair with another computation to test
  /// that the continuation chain doesn't interfere with other data.
  static inline const std::pair<unsigned int, unsigned int> test_pair = []() {
    tree t = build_left(4u);
    unsigned int s = tree_sum(t);
    unsigned int f = tree_fold_cps(
        t, 0u,
        [](const unsigned int &l, const unsigned int &n,
           const unsigned int &r) { return ((l + n) + r); },
        [](unsigned int x) { return x; });
    return std::make_pair(s, f);
  }();
};

#endif // INCLUDED_CPS_CLOSURE_CHAIN
