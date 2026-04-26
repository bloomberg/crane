#ifndef INCLUDED_REUSE_MOVE_SHADOW
#define INCLUDED_REUSE_MOVE_SHADOW

#include <memory>
#include <optional>
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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct ReuseMoveShadow {
  /// Define node FIRST so it gets variant index 0 and the reuse
  /// optimization picks the node branch via List.hd reuse_candidates.
  struct tree {
    // TYPES
    struct Node {
      unsigned int d_a0;
      std::unique_ptr<tree> d_a1;
      std::unique_ptr<tree> d_a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    explicit tree(Leaf _v) : d_v_(_v) {}

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
      if (std::holds_alternative<Node>(_sv.v())) {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(Node{d_a0, clone_value(d_a1), clone_value(d_a2)});
      } else {
        return tree(Leaf{});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree node(unsigned int a0, const tree &a1,
                                           const tree &a2) {
      return tree(Node{std::move(a0), std::make_unique<tree>(a1),
                       std::make_unique<tree>(a2)});
    }

    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

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

  template <typename T1, MapsTo<T1, unsigned int, tree, T1, tree, T1> F0>
  static T1 tree_rect(F0 &&f, const T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f(d_a0, *(d_a1), tree_rect<T1>(f, f0, *(d_a1)), *(d_a2),
               tree_rect<T1>(f, f0, *(d_a2)));
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, tree, T1, tree, T1> F0>
  static T1 tree_rec(F0 &&f, const T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f(d_a0, *(d_a1), tree_rec<T1>(f, f0, *(d_a1)), *(d_a2),
               tree_rec<T1>(f, f0, *(d_a2)));
    } else {
      return f0;
    }
  }

  __attribute__((pure)) static unsigned int tree_sum(const tree &t);
  /// BUG: The reuse branch does not shift move_dead_after or
  /// move_owned_vars when pushing pattern variables.
  ///
  /// In dup_left, the parameter t is at de Bruijn index 2, and is owned
  /// (escapes in the else branch).  After pushing 3 pattern variables
  /// (v at 1, l at 2, r at 3), the pattern variable l lands at index 2 —
  /// colliding with the un-shifted index for t in move_dead_after and
  /// move_owned_vars.
  ///
  /// The non-reuse path correctly calls with_shifted_move_tracking which
  /// shifts both sets by n_pat_vars and clears move_dead_after.  But the
  /// reuse path (lines ~4537-4602 in translation.ml) calls
  /// process_match_pattern_vars WITHOUT shifting.
  ///
  /// Since l appears TWICE in the body (node v l l), the assign loop
  /// generates gen_expr body_env (MLrel 2) for each.  Both checks hit
  /// move_dead_after and move_owned_vars at index 2 (thinking it refers to
  /// the dead/owned t), so both emit std::move(l):
  ///
  /// _rf.d_a1 = std::move(l);   // l moved, now null
  /// _rf.d_a2 = std::move(l);   // l is null!  assigns null
  ///
  /// The returned tree has d_a2 = nullptr.  Traversing the right subtree
  /// crashes with a null-pointer dereference.
  __attribute__((pure)) static tree dup_left(tree t, const bool &b);
  /// test1: dup_left (node 10 (node 1 leaf leaf) (node 2 leaf leaf)) true
  /// Expected result: node 10 (node 1 leaf leaf) (node 1 leaf leaf)
  /// tree_sum = 10 + 1 + 0 + 0 + 1 + 0 + 0 = 12
  /// BUG: right subtree is null -> crash in tree_sum.
  static inline const unsigned int test1 = tree_sum(
      dup_left(tree::node(10u, tree::node(1u, tree::leaf(), tree::leaf()),
                          tree::node(2u, tree::leaf(), tree::leaf())),
               true));
  /// test2: Deeper tree to stress memory.
  /// dup_left (node 5 (node 3 (node 4 leaf leaf) leaf) leaf) true
  /// Expected: node 5 (node 3 (node 4 leaf leaf) leaf) (node 3 (node 4 leaf
  /// leaf) leaf) tree_sum = 5 + (3 + 4 + 0) + (3 + 4 + 0) = 19 BUG: right
  /// subtree is null -> crash.
  static inline const unsigned int test2 = tree_sum(dup_left(
      tree::node(5u,
                 tree::node(3u, tree::node(4u, tree::leaf(), tree::leaf()),
                            tree::leaf()),
                 tree::leaf()),
      true));
  /// test3: Non-reuse path (use_count > 1).
  /// This should work correctly because the normal branch uses
  /// with_shifted_move_tracking which properly shifts the indices.
  static inline const unsigned int test3 = []() {
    tree t = tree::node(7u, tree::node(8u, tree::leaf(), tree::leaf()),
                        tree::node(9u, tree::leaf(), tree::leaf()));
    return (tree_sum(dup_left(t, true)) + tree_sum(t));
  }();
};

#endif // INCLUDED_REUSE_MOVE_SHADOW
