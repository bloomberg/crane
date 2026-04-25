#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

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

struct MutualRecursion {
  __attribute__((pure)) static bool is_even(const unsigned int &n);
  __attribute__((pure)) static bool is_odd(const unsigned int &n);
  template <typename t_A> struct tree;
  template <typename t_A> struct forest;

  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {
      t_A d_a0;
    };

    struct Node {
      std::unique_ptr<forest<t_A>> d_a0;
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

    tree(const tree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree<t_A> &operator=(const tree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree<t_A> &operator=(tree<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return tree<t_A>(Leaf{clone_as_value<t_A>(d_a0)});
      } else {
        const auto &[d_a0] = std::get<Node>(_sv.v());
        return tree<t_A>(
            Node{clone_as_value<std::unique_ptr<forest<t_A>>>(d_a0)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) tree<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return tree<_CloneT0>(
            typename tree<_CloneT0>::Leaf{clone_as_value<_CloneT0>(d_a0)});
      } else {
        const auto &[d_a0] = std::get<Node>(_sv.v());
        return tree<_CloneT0>(typename tree<_CloneT0>::Node{
            clone_as_value<std::unique_ptr<forest<_CloneT0>>>(d_a0)});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree<t_A> leaf(t_A a0) {
      return tree(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static tree<t_A> node(const forest<t_A> &a0) {
      return tree(Node{std::make_unique<forest<t_A>>(a0.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> *operator->() { return this; }

    __attribute__((pure)) const tree<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename t_A> struct forest {
    // TYPES
    struct Empty {};

    struct Trees {
      std::unique_ptr<tree<t_A>> d_a0;
      std::unique_ptr<forest<t_A>> d_a1;
    };

    using variant_t = std::variant<Empty, Trees>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(Empty _v) : d_v_(_v) {}

    explicit forest(Trees _v) : d_v_(std::move(_v)) {}

    forest(const forest<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    forest(forest<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) forest<t_A> &operator=(const forest<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) forest<t_A> &operator=(forest<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) forest<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Empty>(_sv.v())) {
        return forest<t_A>(Empty{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Trees>(_sv.v());
        return forest<t_A>(
            Trees{clone_as_value<std::unique_ptr<tree<t_A>>>(d_a0),
                  clone_as_value<std::unique_ptr<forest<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) forest<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Empty>(_sv.v())) {
        return forest<_CloneT0>(typename forest<_CloneT0>::Empty{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Trees>(_sv.v());
        return forest<_CloneT0>(typename forest<_CloneT0>::Trees{
            clone_as_value<std::unique_ptr<tree<_CloneT0>>>(d_a0),
            clone_as_value<std::unique_ptr<forest<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static forest<t_A> empty() { return forest(Empty{}); }

    __attribute__((pure)) static forest<t_A> trees(const tree<t_A> &a0,
                                                   const forest<t_A> &a1) {
      return forest(Trees{std::make_unique<tree<t_A>>(a0.clone()),
                          std::make_unique<forest<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) forest<t_A> *operator->() { return this; }

    __attribute__((pure)) const forest<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = forest<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, forest<T1>> F1>
  static T2 tree_rect(F0 &&f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename tree<T1>::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, forest<T1>> F1>
  static T2 tree_rec(F0 &&f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename tree<T1>::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, tree<T1>, forest<T1>, T2> F1>
  static T2 forest_rect(const T2 f, F1 &&f0, const forest<T1> &f1) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest<T1>::Trees>(f1.v());
      return f0(*(d_a0), *(d_a1), forest_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, tree<T1>, forest<T1>, T2> F1>
  static T2 forest_rec(const T2 f, F1 &&f0, const forest<T1> &f1) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest<T1>::Trees>(f1.v());
      return f0(*(d_a0), *(d_a1), forest_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int tree_size(const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return 1u;
    } else {
      const auto &[d_a0] = std::get<typename tree<T1>::Node>(t.v());
      return forest_size<T1>(*(d_a0));
    }
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int forest_size(const forest<T1> &f) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest<T1>::Trees>(f.v());
      return (tree_size<T1>(*(d_a0)) + forest_size<T1>(*(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const tree<unsigned int> &t);
  __attribute__((pure)) static unsigned int
  forest_sum(const forest<unsigned int> &f);
  static inline const bool test_even_0 = is_even(0u);
  static inline const bool test_even_4 = is_even(4u);
  static inline const bool test_odd_3 = is_odd(3u);
  static inline const bool test_odd_4 = is_odd(4u);
  static inline const tree<unsigned int> simple_tree =
      tree<unsigned int>::node(forest<unsigned int>::trees(
          tree<unsigned int>::leaf(1u),
          forest<unsigned int>::trees(tree<unsigned int>::leaf(2u),
                                      forest<unsigned int>::empty())));
  static inline const tree<unsigned int> nested_tree =
      tree<unsigned int>::node(forest<unsigned int>::trees(
          tree<unsigned int>::node(forest<unsigned int>::trees(
              tree<unsigned int>::leaf(3u), forest<unsigned int>::empty())),
          forest<unsigned int>::trees(tree<unsigned int>::leaf(4u),
                                      forest<unsigned int>::empty())));
  static inline const unsigned int test_size_simple =
      tree_size<unsigned int>(simple_tree);
  static inline const unsigned int test_size_nested =
      tree_size<unsigned int>(nested_tree);
  static inline const unsigned int test_sum_simple = tree_sum(simple_tree);
  static inline const unsigned int test_sum_nested = tree_sum(nested_tree);
};

#endif // INCLUDED_MUTUAL_RECURSION
