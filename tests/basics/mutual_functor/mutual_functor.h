#ifndef INCLUDED_MUTUAL_FUNCTOR
#define INCLUDED_MUTUAL_FUNCTOR

#include <concepts>
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

template <typename M>
concept Elem = requires {
  typename M::t;
  requires(
      requires {
        { M::dflt } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::dflt() } -> std::convertible_to<typename M::t>;
      });
};

template <Elem E> struct MutualTree {
  struct tree;
  struct forest;

  struct tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      unsigned int d_a0;
      std::unique_ptr<forest> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

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
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return tree(Leaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
        return tree(Node{d_a0, clone_value(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf(unsigned int a0) {
      return tree(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static tree node(unsigned int a0, const forest &a1) {
      return tree(Node{std::move(a0), std::make_unique<forest>(a1)});
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

  struct forest {
    // TYPES
    struct FNil {};

    struct FCons {
      std::unique_ptr<tree> d_a0;
      std::unique_ptr<forest> d_a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(FNil _v) : d_v_(_v) {}

    explicit forest(FCons _v) : d_v_(std::move(_v)) {}

    forest(const forest &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    forest(forest &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) forest &operator=(const forest &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) forest &operator=(forest &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) forest clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<FNil>(_sv.v())) {
        return forest(FNil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<FCons>(_sv.v());
        return forest(FCons{clone_value(d_a0), clone_value(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static forest fnil() { return forest(FNil{}); }

    __attribute__((pure)) static forest fcons(const tree &a0,
                                              const forest &a1) {
      return forest(
          FCons{std::make_unique<tree>(a0), std::make_unique<forest>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) forest *operator->() { return this; }

    __attribute__((pure)) const forest *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = forest(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, forest> F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0.v());
      return f0(d_a0, *(d_a1));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, forest> F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0.v());
      return f0(d_a0, *(d_a1));
    }
  }

  template <typename T1, MapsTo<T1, tree, forest, T1> F1>
  static T1 forest_rect(const T1 f, F1 &&f0, const forest &f1) {
    if (std::holds_alternative<typename forest::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f1.v());
      return f0(*(d_a0), *(d_a1), forest_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, tree, forest, T1> F1>
  static T1 forest_rec(const T1 f, F1 &&f0, const forest &f1) {
    if (std::holds_alternative<typename forest::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f1.v());
      return f0(*(d_a0), *(d_a1), forest_rec<T1>(f, f0, *(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int tree_size(const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      return 1u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0.v());
      return (1u + forest_size(*(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int forest_size(const forest &f) {
    if (std::holds_alternative<typename forest::FNil>(f.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f.v());
      return (tree_size(*(d_a0)) + forest_size(*(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int tree_sum(const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0.v());
      return d_a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0.v());
      return (d_a0 + forest_sum(*(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int forest_sum(const forest &f) {
    if (std::holds_alternative<typename forest::FNil>(f.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f.v());
      return (tree_sum(*(d_a0)) + forest_sum(*(d_a1)));
    }
  }

  static const tree &leaf1() {
    static const tree v = tree::leaf(1u);
    return v;
  }

  static const tree &leaf2() {
    static const tree v = tree::leaf(2u);
    return v;
  }

  static const forest &small_forest() {
    static const forest v =
        forest::fcons(leaf1(), forest::fcons(leaf2(), forest::fnil()));
    return v;
  }

  static const tree &sample_tree() {
    static const tree v = tree::node(0u, small_forest());
    return v;
  }
};

struct NatElem {
  using t = unsigned int;
  static inline const unsigned int dflt = 0u;
};

static_assert(Elem<NatElem>);
using NatTree = MutualTree<NatElem>;
const unsigned int test_tree_size = NatTree::tree_size(NatTree::sample_tree());
const unsigned int test_forest_size =
    NatTree::forest_size(NatTree::small_forest());
const unsigned int test_tree_sum = NatTree::tree_sum(NatTree::sample_tree());

#endif // INCLUDED_MUTUAL_FUNCTOR
